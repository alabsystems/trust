// trust-router/strengthen_whole_program.rs: R1 whole-program caller-propagation —
// the PURE, fail-closed decision over a reverse call graph + per-caller discharge
// verdicts. This is the designed verdict-flipping track, but currently admits
// none. Its structural model would admit an inferred precondition P on a callee
// F only when EVERY caller establishes P (assume-guarantee). A single
// uncovered/indirect call ⇒ reject (assuming P unproven at one
// entry would discharge a FALSE VC — the catastrophic case). The compiler-side
// driver builds the inputs (substitution, guards, router verdicts, coverage); this
// module owns the soundness decision so it can be unit-tested on stock cargo.
//
// STATUS: LIVE, on sealed kernel-replayed evidence.
//
// The 72ada1163c audit hard-blocked this lane for a correct reason: the decision
// read PUBLIC assurance labels (`AssuranceLevel::Certified`,
// `VerificationResult::Proved`), which are ordinary constructible data. A label
// is not a proof, so no label may authorize a flip.
//
// The restoration does not weaken that finding — it supplies what the finding
// demanded. `mint_caller_propagation_certificate` is now the sole decision entry
// and the sole constructor of the private, unforgeable
// `SealedCallerPropagationCertificate`. It never reads an assurance label.
// Instead it REPLAYS every certificate it binds through the clean CIC kernel
// (`trust_certify::replay_vc_evidence`): the kernel re-checks the proof term
// against a hypothesis context rebuilt from the obligation's OWN atoms, bound to
// that obligation's full identity (function + kind + location + formula), under a
// strict axiom-closure gate that rejects `sorry`/`trustedAy`/`trustedArith`
// oracle shortcuts. It additionally closes two holes the pre-audit gate had, which
// no label check would have caught: the strengthened obligation must structurally
// BE `V ∧ P` (not a real proof of a different VC), and the discharged call sites
// must be EXACTLY the enumerated caller set (not whatever list the driver passed).
//
// The iterative single-function strengthening loop (trust-loop / trust-strengthen:
// abstract domains + CEGIS + LLM proposers) is a DIFFERENT lane with no sealed
// evidence carrier, and stays hard-blocked behind its own switch —
// `strengthen_gate::STRENGTHENING_AUTHORITY_AVAILABLE`. The two must never be
// fused again: sharing a switch would make R1's evidence story silently activate
// a CEGIS/LLM proposer inside the shipped compiler.

use sha2::{Digest, Sha256};
use trust_types::call_graph::CallGraph;
use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{Formula, SourceSpan, VerificationCondition, VerificationResult};

/// Why F's callers cannot be proven exhaustive. Any non-empty set ⇒ reject.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CoverageGap {
    ExternallyReachable,
    IndirectCall {
        detail: String,
    },
    UnresolvedCallee {
        name: String,
    },
    Recursive,
    /// The whole-crate caller scan itself could not account for the crate, so NO
    /// function's caller set is provably exhaustive. Crate-level, not about F: an
    /// unscannable body or a `global_asm!` item says nothing about F's visibility.
    ///
    /// Why this variant exists: the oracle used to fold that poison into
    /// `is_public`, from which this function could only classify it as
    /// [`CoverageGap::ExternallyReachable`]. No consumer ever rendered that
    /// classification — the compiler's sole call site collapses the returned gap
    /// list to a Total/not-Total test and drops it — so the shipped defect was
    /// SILENCE: the cause of a crate-wide R1 rejection was stated nowhere.
    /// Carrying the scan's own words through classification is what lets the one
    /// real reporting consumer (the compiler's crate-level warning) name the true
    /// cause, and keeps any future gap consumer from reading a conflated
    /// external-reachability claim. `reason` is the oracle's rendering, verbatim.
    ScanIncomplete {
        reason: String,
    },
}

/// Provable exhaustiveness of F's call sites.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CallerCoverage {
    Total,
    Incomplete(Vec<CoverageGap>),
}

/// Rustc-derived danger signals the pure graph cannot see (GREENFIELD to compute).
///
/// `#[non_exhaustive]` is load-bearing: no field subset is a sufficient rejection
/// test. The crate-scan poison travels ONLY in `scan_incomplete` — it is
/// deliberately NOT folded into `is_public` any more — so a consumer that reads
/// `is_public || address_taken` as "the old conservative bool" is unsound.
/// [`classify_coverage`] is the sole judge of whether these signals permit
/// `Total`; ask it, never re-derive the decision from fields. Out-of-crate
/// producers must construct through [`CoverageSignals::new`], whose signature
/// names every hazard channel so a newly added channel cannot be silently
/// defaulted at any production site.
#[non_exhaustive]
#[derive(Debug, Clone, Default)]
pub struct CoverageSignals {
    pub is_public: bool,
    pub address_taken: bool,
    /// Callee strings at some call site that did not resolve to a node but could be F.
    pub unresolved_callees: Vec<String>,
    /// Reasons the CRATE-WIDE caller scan is not exhaustive (an unscannable body, a
    /// `global_asm!` item). Non-empty ⇒ reject: [`classify_coverage`] turns each
    /// reason into a [`CoverageGap::ScanIncomplete`], a rejection exactly as hard
    /// as the oracle's old `incomplete`-bool fold into `is_public` was — but the
    /// cause survives classification instead of being conflated with external
    /// reachability (which none of these causes establishes). Empty for a
    /// complete scan.
    pub scan_incomplete: Vec<String>,
}

impl CoverageSignals {
    /// The only out-of-crate constructor (`#[non_exhaustive]` forbids literal and
    /// functional-update construction there). Every hazard channel is a required
    /// argument: adding a channel changes this signature, so each producer must
    /// then decide what to pass — the failure mode this closes is a producer
    /// narrowing one channel (as `is_public` was narrowed to exclude the scan
    /// poison) while another construction site silently keeps defaulting it.
    #[must_use]
    pub fn new(
        is_public: bool,
        address_taken: bool,
        unresolved_callees: Vec<String>,
        scan_incomplete: Vec<String>,
    ) -> Self {
        Self { is_public, address_taken, unresolved_callees, scan_incomplete }
    }
}

/// Reasons R1 declines to flip F (each ⇒ F keeps its honest Failed/Unknown).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum R1Reject {
    Disconnected,
    StrengthenedNotCertified,
    /// The strengthened obligation's certificate did not REPLAY: the clean kernel
    /// would not re-check its term against a context rebuilt from that
    /// obligation's own atoms (or the identity binding / axiom-closure gate
    /// rejected it). A public `Certified` label is not evidence.
    StrengthenedNotReplayed,
    /// The strengthened obligation is not `V ∧ P` (+ at most the declared
    /// contract) at V's own kind/location — i.e. a real proof of the WRONG thing.
    StrengthenedFormulaMismatch,
    NotNecessary,
    CoverageIncomplete(Vec<CoverageGap>),
    NoCallers,
    /// The discharged call sites are not exactly the enumerated caller set — a
    /// caller was dropped (or invented) between the call-graph oracle and the
    /// discharge loop. Assuming P at an entry that never establishes it is the
    /// catastrophic case, so this is fail-closed.
    CallerSetMismatch {
        expected: Vec<String>,
        covered: Vec<String>,
    },
    CallerUndischarged {
        caller: String,
        call_site: SourceSpan,
    },
    CallerFormulaMismatch {
        caller: String,
        call_site: SourceSpan,
    },
    /// A call site's discharge certificate did not REPLAY (see
    /// [`R1Reject::StrengthenedNotReplayed`]).
    CallerNotReplayed {
        caller: String,
        call_site: SourceSpan,
    },
    /// Two SCC member bundles claim the same def_path — the per-member invariant
    /// lookup would be ambiguous, so the whole SCC is rejected.
    InductiveMemberDuplicate {
        member: String,
    },
    /// An inductive-step row names a discharging caller that is not an SCC
    /// member, or an enumerated BASE-CASE caller IS an SCC member (an intra-SCC
    /// edge smuggled into the unconditional base case).
    InductiveCallerNotMember {
        member: String,
        caller: String,
    },
    /// A discharge's allowed guard equals a member invariant that the
    /// discharging caller is not entitled to assume: any member invariant in a
    /// BASE-CASE guard list (the base case must be unconditional), or another
    /// member's invariant in an INDUCTIVE-STEP guard list (the hypothesis may
    /// only be the discharging caller's own `P`).
    InductiveForeignHypothesis {
        member: String,
        caller: String,
    },
    /// An SCC member has neither an external caller nor an intra-SCC recursive
    /// call into it — its `P` is established nowhere and preserved by nothing.
    InductiveMemberUnconstrained {
        member: String,
    },
    /// A dominance claim names one caller while carrying a different extracted
    /// function body.  The name participates in exact coverage; the body is the
    /// object re-analysed, so accepting a mismatch would let a dominated helper
    /// stand in for an uncovered caller.
    DominatedCallerIdentityMismatch {
        claimed: String,
        actual: String,
    },
    /// The whole SCC has ZERO external call sites — the induction has no base
    /// case grounding it at any real entry.
    InductiveUngrounded,
    /// [`seal_generic_flip`] was handed a token whose provenance is not
    /// [`SealedCertificateProvenance::DirectCallerPropagation`]. Per-mono
    /// aggregation is defined over direct tokens only; aggregating a
    /// conditional (inductive) token would launder its hypothesis away.
    GenericAggregationOfNonDirectToken,
}

/// The per-call structural check (R1's variant of `discharge_formula_ok`). Accepts
/// ONLY bare `¬(P[σ])`, or `And(conjuncts)` with `¬(P[σ])` present and every other
/// conjunct in `allowed_guards`. Any other shape ⇒ reject (fail-closed).
#[must_use]
pub fn is_admissible_caller_discharge(
    obligation: &Formula,
    assumption_substituted: &Formula,
    allowed_guards: &[Formula],
) -> bool {
    let not_p = Formula::Not(Box::new(assumption_substituted.clone()));
    if *obligation == not_p {
        return true;
    }
    let Formula::And(conjuncts) = obligation else {
        return false;
    };
    conjuncts.contains(&not_p)
        && conjuncts.iter().all(|c| *c == not_p || allowed_guards.contains(c))
}

/// Reverse call graph: callee def_path -> caller def_paths (deduplicated).
#[must_use]
pub fn reverse_call_graph(g: &CallGraph) -> FxHashMap<String, Vec<String>> {
    let mut rev: FxHashMap<String, Vec<String>> = FxHashMap::default();
    for n in &g.nodes {
        rev.entry(n.def_path.clone()).or_default();
    }
    for e in &g.edges {
        let v = rev.entry(e.callee.clone()).or_default();
        if !v.contains(&e.caller) {
            v.push(e.caller.clone());
        }
    }
    rev
}

/// Enumerate (caller, call_site) edges into F.
#[must_use]
pub fn callers_of(g: &CallGraph, f: &str) -> Vec<(String, SourceSpan)> {
    g.edges
        .iter()
        .filter(|e| e.callee == f)
        .map(|e| (e.caller.clone(), e.call_site.clone()))
        .collect()
}

/// Classify whether F's callers can be proven exhaustive. PURE over the graph +
/// rustc danger signals; sound only when `signals` is computed soundly (GREENFIELD).
#[must_use]
pub fn classify_coverage(
    f: &str,
    recursive: &FxHashSet<String>,
    signals: &CoverageSignals,
) -> CallerCoverage {
    let mut gaps = Vec::new();
    // Crate-level first: when the scan itself is poisoned, that — not anything about
    // F — is the dominant reason no caller set is exhaustive.
    for reason in &signals.scan_incomplete {
        gaps.push(CoverageGap::ScanIncomplete { reason: reason.clone() });
    }
    if signals.is_public {
        gaps.push(CoverageGap::ExternallyReachable);
    }
    if signals.address_taken {
        gaps.push(CoverageGap::IndirectCall { detail: "address-taken (fn-ptr/dyn)".into() });
    }
    if recursive.contains(f) {
        gaps.push(CoverageGap::Recursive);
    }
    for name in &signals.unresolved_callees {
        gaps.push(CoverageGap::UnresolvedCallee { name: name.clone() });
    }
    if gaps.is_empty() { CallerCoverage::Total } else { CallerCoverage::Incomplete(gaps) }
}

/// Exact identity of one obligation a sealed certificate is evidence about.
///
/// Deliberately NOT a fixed-width digest: a hash collision must never donate
/// proof authority (the same rule `ExactResultRowIdentity` follows in
/// `trust_verify.rs`). Equality is over the exact canonical payload; the
/// `digest` is derived from it for logging/reporting only.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SealedVcIdentity {
    function: String,
    kind_desc: String,
    file: String,
    line: u32,
    col: u32,
    canonical_formula: String,
}

impl SealedVcIdentity {
    fn of(vc: &VerificationCondition) -> Self {
        Self {
            function: vc.function.as_str().to_string(),
            kind_desc: vc.kind.description(),
            file: vc.location.file.clone(),
            line: vc.location.line_start,
            col: vc.location.col_start,
            canonical_formula: format!("{:?}", vc.formula),
        }
    }

    /// SHA-256 over the exact canonical payload. For display/reporting ONLY —
    /// authority always compares the payload itself.
    #[must_use]
    pub fn digest(&self) -> String {
        let mut h = Sha256::new();
        h.update(b"trust-router.r1.sealed-vc-identity.v1");
        for field in [
            self.function.as_bytes(),
            self.kind_desc.as_bytes(),
            self.file.as_bytes(),
            &self.line.to_le_bytes(),
            &self.col.to_le_bytes(),
            self.canonical_formula.as_bytes(),
        ] {
            h.update((field.len() as u64).to_le_bytes());
            h.update(field);
        }
        format!("{:x}", h.finalize())
    }

    /// The STABLE per-operation key: kind + file + start line/col, dropping the
    /// violation formula.
    ///
    /// Why the formula is excluded HERE: the R1 harvest runs on pre-optimization
    /// MIR while the flip seam runs on post-optimization MIR, so the violation
    /// formula's SSA versioning shifts (`_4#s0_3`) even though the obligation is
    /// the same source operation. The source location does not shift. The
    /// certificate still BINDS the exact pre-opt formula (that is what was
    /// proved); this key is only how the flip seam recognizes the row, and it is
    /// guarded by the seam's ambiguity refusal (two same-kind operations on one
    /// line ⇒ apply to NEITHER — see `reject_two_divisions_one_line`).
    #[must_use]
    pub fn matches_operation(&self, kind_desc: &str, file: &str, line: u32, col: u32) -> bool {
        self.kind_desc == kind_desc
            && self.line == line
            && self.col == col
            && Self::file_matches(&self.file, file)
    }

    fn file_matches(a: &str, b: &str) -> bool {
        if a == b {
            return true;
        }
        let pa: Vec<_> = std::path::Path::new(a).components().collect();
        let pb: Vec<_> = std::path::Path::new(b).components().collect();
        pa.len().min(pb.len()) >= 2 && pa.iter().rev().zip(pb.iter().rev()).all(|(x, y)| x == y)
    }
}

/// THE SEALED TOKEN. Possessing one is proof that
/// [`mint_caller_propagation_certificate`] ran every soundness check below —
/// including a KERNEL REPLAY of every certificate it binds.
///
/// UNFORGEABLE BY CONSTRUCTION: every field is private, there is no public
/// constructor, no `Default`, no deserialization, and no `pub` struct-literal
/// path. The ONLY code in the workspace that can produce a value of this type
/// is in this module, and each producer witnesses the same end claim —
/// *attributing `Proved` to the bound discharge obligation is sound* — by a
/// fully kernel-replayed argument:
///
///  * [`mint_caller_propagation_certificate`] — the DIRECT assume-guarantee
///    case (every caller establishes `P`, unconditionally); the checks below.
///  * [`seal_generic_flip`] — aggregation over per-monomorphization tokens each
///    already minted by `mint_caller_propagation_certificate`.
///  * [`mint_inductive_caller_propagation_certificate`] — the INDUCTIVE case
///    for a recursive SCC (base case at every external entry + preservation at
///    every intra-SCC call), with its own written soundness argument.
///
/// `mint_caller_propagation_certificate` returns `Err` unless:
///
///  1. coverage is provably `Total` (F is not externally reachable and every
///     caller is enumerable — the rustc-side oracle's judgment);
///  2. the original obligation genuinely `Failed` (necessity);
///  3. `P` is CONNECTED to `V` (its free variables are a non-empty subset);
///  4. the STRENGTHENED VC really is `V ∧ P` (+ at most the declared contract) at
///     the SAME kind/location — not some other obligation's proof;
///  5. the strengthened VC's certificate REPLAYS: the clean kernel re-checks its
///     CIC term against a context rebuilt from that obligation's own atoms, bound
///     to its full identity, under the strict axiom-closure gate;
///  6. the caller obligations cover EXACTLY the enumerated caller set (no caller
///     silently dropped);
///  7. every caller obligation is structurally `¬P[σ]` (+ allowed guards), and
///     its certificate REPLAYS under the same criterion.
///
/// A public `VerificationResult::Proved` / `AssuranceLevel::Certified` label
/// grants NOTHING here — the labels are not even read. That is the specific
/// defect this type exists to fix: labels are public data, so the previous gate
/// (which trusted them) could be satisfied by forged verdicts.
///
/// SOUNDNESS ARGUMENT the token witnesses. Let `F` have violation `V` at
/// operation `O`, unprovable in isolation. From (5), `P ∧ V` is UNSAT: assuming
/// `P` at entry, `O` cannot violate. From (7), every call site of `F` establishes
/// `P`. From (1) and (6), those call sites are ALL the ways `F` is ever entered.
/// Therefore `P` holds at entry on every real execution, so `O` never violates,
/// and attributing `Proved` to `V` is sound. Every step is kernel-checked; the
/// only non-kernel inputs are the rustc oracle's coverage judgment and vcgen's
/// substitution `σ` — both already in the trusted base that generated `V` itself.
#[derive(Debug, Clone)]
pub struct SealedCallerPropagationCertificate {
    /// The ORIGINAL, isolated obligation being flipped (`V`).
    discharge: SealedVcIdentity,
    /// The obligation actually PROVED (`V ∧ P`, + at most the declared contract).
    strengthened: SealedVcIdentity,
    /// Every enumerated call site's discharge obligation (`¬P[σ]`), all replayed.
    caller_sites: Vec<SealedVcIdentity>,
    /// The callers covered — exactly the enumerated caller set.
    covered_callers: Vec<String>,
    /// The inferred precondition `P`.
    assumption: Formula,
    /// Which mint produced this token (what argument form the covered callers
    /// witness) — see [`SealedCertificateProvenance`].
    provenance: SealedCertificateProvenance,
}

/// Which mint produced a sealed token — i.e. WHAT ARGUMENT FORM its covered
/// callers witness. The END CLAIM is identical across variants (attributing
/// `Proved` to the bound discharge obligation is sound), but a consumer must
/// NOT read [`SealedCallerPropagationCertificate::covered_callers`] as "each of
/// these discharged `¬P[σ]` unconditionally" without checking this: under
/// [`SealedCertificateProvenance::InductiveSccPropagation`] the intra-SCC
/// entries discharged their obligation only UNDER their own inductive
/// hypothesis.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SealedCertificateProvenance {
    /// [`mint_caller_propagation_certificate`]: every covered caller
    /// discharged `¬P[σ]` unconditionally (the direct assume-guarantee case).
    DirectCallerPropagation,
    /// [`seal_generic_flip`]: the union over per-monomorphization DIRECT
    /// tokens of a closed-world generic (each mono's callers unconditional).
    GenericMonoAggregation,
    /// [`mint_inductive_caller_propagation_certificate`]: base-case (external)
    /// callers discharged unconditionally; intra-SCC callers discharged under
    /// their own member's inductive hypothesis, admitted only inside the
    /// checked whole-SCC induction.
    InductiveSccPropagation,
}

impl SealedCallerPropagationCertificate {
    /// The original obligation this certificate authorizes a flip of.
    #[must_use]
    pub fn discharge_identity(&self) -> &SealedVcIdentity {
        &self.discharge
    }

    /// The obligation that was actually proved.
    #[must_use]
    pub fn strengthened_identity(&self) -> &SealedVcIdentity {
        &self.strengthened
    }

    #[must_use]
    pub fn assumption(&self) -> &Formula {
        &self.assumption
    }

    /// The callers the token covers. HOW each was discharged depends on
    /// [`Self::provenance`]: under
    /// [`SealedCertificateProvenance::InductiveSccPropagation`] the intra-SCC
    /// entries are CONDITIONAL dischargers (under their own hypothesis), not
    /// unconditional ones.
    #[must_use]
    pub fn covered_callers(&self) -> &[String] {
        &self.covered_callers
    }

    /// Which mint produced this token — see [`SealedCertificateProvenance`].
    #[must_use]
    pub fn provenance(&self) -> SealedCertificateProvenance {
        self.provenance
    }

    #[must_use]
    pub fn caller_site_count(&self) -> usize {
        self.caller_sites.len()
    }

    /// Whether this token authorizes flipping the obligation of kind `kind_desc`
    /// at `file:line:col`. See [`SealedVcIdentity::matches_operation`] for why the
    /// violation formula cannot be part of this key across the pre-opt/post-opt
    /// MIR boundary.
    #[must_use]
    pub fn authorizes_operation(&self, kind_desc: &str, file: &str, line: u32, col: u32) -> bool {
        self.discharge.matches_operation(kind_desc, file, line, col)
    }

    /// The verdict this token authorizes for the bound discharge obligation.
    ///
    /// The `Proved` value is produced HERE, by the token, so a flip's verdict
    /// cannot be conjured anywhere else: the seam that applies it has nothing to
    /// write unless it is holding a sealed certificate. The end claim is a
    /// compiler-composed closed-world derivation over kernel-replayed component
    /// proofs, not an exact isolated-VC kernel theorem, so it is deductive rather
    /// than reported as SMT-certified.
    #[must_use]
    pub fn attributed_verdict(&self) -> VerificationResult {
        VerificationResult::Proved {
            solver: "ay+clean-kernel (R1 caller propagation)".into(),
            time_ms: 0,
            strength: trust_types::ProofStrength::deductive(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        }
    }

    /// Stable digest of the whole sealed decision (both bound VC digests + every
    /// replayed call site). Reporting only.
    #[must_use]
    pub fn digest(&self) -> String {
        let mut h = Sha256::new();
        h.update(b"trust-router.r1.sealed-certificate.v1");
        for d in [self.discharge.digest(), self.strengthened.digest()] {
            h.update(d.as_bytes());
        }
        for site in &self.caller_sites {
            h.update(site.digest().as_bytes());
        }
        format!("{:x}", h.finalize())
    }
}

/// Seal a flip for a CLOSED-WORLD GENERIC F from the per-monomorphization
/// certificates.
///
/// A generic F has ONE un-monomorphized body (and so one Failed VC) but many
/// monos, each with its own concrete violation and its own caller set. Flipping
/// the generic body's obligation asserts safety for ALL of them, so this requires
/// a sealed certificate for EVERY observed mono — each minted by
/// [`mint_caller_propagation_certificate`], i.e. each already kernel-replayed.
///
/// The monos must all pin the SAME source operation (kind + file + line + col):
/// they are all the same generic body, so a divergence means they fail at
/// DIFFERENT operations, which one generic VC cannot faithfully represent.
///
/// SOUND because the caller's oracle (`generic_mono_coverable`) established F is
/// closed in-crate, so the observed monos are ALL the monos there are. The
/// returned token authorizes the shared operation and carries the union of every
/// mono's replayed call sites.
pub fn seal_generic_flip(
    monos: Vec<SealedCallerPropagationCertificate>,
) -> Result<SealedCallerPropagationCertificate, R1Reject> {
    let Some(first) = monos.first() else {
        return Err(R1Reject::NoCallers);
    };
    // Aggregation is defined over DIRECT tokens only: each mono's callers
    // discharged unconditionally. An inductive (or already-aggregated) token
    // here would launder a conditional discharge into the union — refuse.
    if !monos.iter().all(|m| m.provenance == SealedCertificateProvenance::DirectCallerPropagation) {
        return Err(R1Reject::GenericAggregationOfNonDirectToken);
    }
    let op = &first.discharge;
    if !monos
        .iter()
        .all(|m| m.discharge.matches_operation(&op.kind_desc, &op.file, op.line, op.col))
    {
        return Err(R1Reject::StrengthenedFormulaMismatch);
    }
    let mut caller_sites = Vec::new();
    let mut covered_callers = Vec::new();
    for m in &monos {
        caller_sites.extend(m.caller_sites.iter().cloned());
        covered_callers.extend(m.covered_callers.iter().cloned());
    }
    covered_callers.sort();
    covered_callers.dedup();
    Ok(SealedCallerPropagationCertificate {
        discharge: first.discharge.clone(),
        strengthened: first.strengthened.clone(),
        caller_sites,
        covered_callers,
        assumption: first.assumption.clone(),
        provenance: SealedCertificateProvenance::GenericMonoAggregation,
    })
}

/// The strengthened obligation (`V ∧ P`) and the certificate proving it.
pub struct StrengthenedProof<'a> {
    pub vc: &'a VerificationCondition,
    pub evidence: &'a trust_ir::ProofEvidence,
}

/// One enumerated call site's discharge obligation (`¬P[σ]`) and its certificate.
pub struct CallerDischargeProof<'a> {
    pub caller: String,
    pub call_site: SourceSpan,
    /// `P[actuals/formals]` — the producer (vcgen) owns σ.
    pub assumption_substituted: Formula,
    /// The exact call-site obligation the certificate is evidence for.
    pub vc: &'a VerificationCondition,
    /// Caller-established guards admissible in `vc.formula`. NEVER free-form.
    pub allowed_guards: Vec<Formula>,
    pub evidence: &'a trust_ir::ProofEvidence,
}

/// Split a formula into its conjuncts (flattening nested `And`).
fn conjuncts_of(f: &Formula) -> Vec<Formula> {
    match f {
        Formula::And(items) => items.iter().flat_map(conjuncts_of).collect(),
        other => vec![other.clone()],
    }
}

/// THE decision, and the ONLY constructor of [`SealedCallerPropagationCertificate`].
///
/// Every check is fail-closed: any `Err` ⇒ no token ⇒ no flip ⇒ the original
/// obligation keeps its honest (Failed) verdict.
#[allow(clippy::too_many_arguments)]
pub fn mint_caller_propagation_certificate(
    original_vc: &VerificationCondition, // the obligation to flip (carries V)
    original_result: &VerificationResult, // its honest, isolated verdict
    assumption: &Formula,                // P (gated to F's parameter namespace)
    gated_requires: &[Formula],          // R — F's declared, gate-approved contract
    strengthened: &StrengthenedProof<'_>, // F's VC re-proved assuming P, + evidence
    coverage: &CallerCoverage,           // the rustc oracle's exhaustiveness judgment
    enumerated_callers: &[String],       // every caller the oracle found
    caller_proofs: &[CallerDischargeProof<'_>], // per-call-site discharge + evidence
) -> Result<SealedCallerPropagationCertificate, R1Reject> {
    let goal_violation = &original_vc.formula;

    // (1) COVERAGE — F must not be reachable by any call site we cannot see.
    //     This is the whole-program side condition: a `pub` fn, a `#[no_mangle]`
    //     symbol, or an address-taken fn can be entered with an arbitrary
    //     argument, so no set of in-crate call sites establishes P.
    if let CallerCoverage::Incomplete(gaps) = coverage {
        return Err(R1Reject::CoverageIncomplete(gaps.clone()));
    }

    // (2) NECESSITY — a genuine counterexample existed. An Unknown/Timeout does
    //     not establish that the strengthening is doing real work, and flipping
    //     it would over-claim.
    if !original_result.is_failed() {
        return Err(R1Reject::NotNecessary);
    }

    // (3) CONNECTEDNESS — P must constrain V's OWN variables. Rejects the #540
    //     vacuity bug (an uninterpreted `__precond_…` atom sharing no symbol with
    //     the goal, which the solver could satisfy freely).
    let avars = assumption.free_variables();
    if avars.is_empty() || !avars.is_subset(&goal_violation.free_variables()) {
        return Err(R1Reject::Disconnected);
    }

    // (4) THE STRENGTHENED VC IS THE RIGHT ONE. A kernel proof of some OTHER
    //     obligation is not evidence about this one. Require the same operation
    //     (kind + location), and require the formula to be exactly
    //     `conjuncts(V) ∪ {P} ∪ (⊆ R)`: it may ADD only the assumption and the
    //     function's own declared contract (which the contract system already
    //     enforces at every call site), and may DROP nothing from V.
    if strengthened.vc.kind.description() != original_vc.kind.description()
        || strengthened.vc.location != original_vc.location
    {
        return Err(R1Reject::StrengthenedFormulaMismatch);
    }
    {
        let s_conj = conjuncts_of(&strengthened.vc.formula);
        let v_conj = conjuncts_of(goal_violation);
        if !s_conj.contains(assumption) {
            return Err(R1Reject::StrengthenedFormulaMismatch);
        }
        if !v_conj.iter().all(|c| s_conj.contains(c)) {
            return Err(R1Reject::StrengthenedFormulaMismatch);
        }
        if !s_conj
            .iter()
            .all(|c| c == assumption || v_conj.contains(c) || gated_requires.contains(c))
        {
            return Err(R1Reject::StrengthenedFormulaMismatch);
        }
    }

    // (5) THE STRENGTHENED PROOF REPLAYS. Not "is labeled Certified" — the clean
    //     kernel re-checks the CIC term against a context rebuilt from this
    //     obligation's own atoms, bound to its full identity, under the strict
    //     axiom-closure gate (no `sorry`/`trustedAy`/`trustedArith` shortcut).
    if !trust_certify::replay_vc_evidence(strengthened.vc, strengthened.evidence) {
        return Err(R1Reject::StrengthenedNotReplayed);
    }

    // (6) EVERY CALLER IS ACCOUNTED FOR. `caller_proofs` must cover exactly the
    //     enumerated caller set — neither missing one (an undischarged entry) nor
    //     inventing one. The old gate iterated whatever list the driver handed it
    //     and never cross-checked it against the call graph; a driver bug that
    //     dropped a caller would have silently produced an unsound flip.
    if enumerated_callers.is_empty() || caller_proofs.is_empty() {
        return Err(R1Reject::NoCallers);
    }
    {
        let mut proved: Vec<&str> = caller_proofs.iter().map(|c| c.caller.as_str()).collect();
        proved.sort_unstable();
        proved.dedup();
        let mut expected: Vec<&str> = enumerated_callers.iter().map(String::as_str).collect();
        expected.sort_unstable();
        expected.dedup();
        if proved != expected {
            return Err(R1Reject::CallerSetMismatch {
                expected: expected.iter().map(|s| (*s).to_string()).collect(),
                covered: proved.iter().map(|s| (*s).to_string()).collect(),
            });
        }
    }

    // (7) EVERY CALL SITE ESTABLISHES P, WITH REPLAYED EVIDENCE.
    let mut caller_sites = Vec::with_capacity(caller_proofs.len());
    for o in caller_proofs {
        // The obligation must be `¬P[σ]`, optionally conjoined with guards the
        // caller itself established. Any other shape proves something else.
        if !is_admissible_caller_discharge(
            &o.vc.formula,
            &o.assumption_substituted,
            &o.allowed_guards,
        ) {
            return Err(R1Reject::CallerFormulaMismatch {
                caller: o.caller.clone(),
                call_site: o.call_site.clone(),
            });
        }
        if !trust_certify::replay_vc_evidence(o.vc, o.evidence) {
            return Err(R1Reject::CallerNotReplayed {
                caller: o.caller.clone(),
                call_site: o.call_site.clone(),
            });
        }
        caller_sites.push(SealedVcIdentity::of(o.vc));
    }

    Ok(SealedCallerPropagationCertificate {
        discharge: SealedVcIdentity::of(original_vc),
        strengthened: SealedVcIdentity::of(strengthened.vc),
        caller_sites,
        covered_callers: enumerated_callers.to_vec(),
        assumption: assumption.clone(),
        provenance: SealedCertificateProvenance::DirectCallerPropagation,
    })
}

/// One intra-SCC recursive call's PRESERVATION obligation and its certificate.
///
/// The obligation is the kernel-replayed UNSAT of
/// `P_caller ∧ path_guards ∧ ¬P_target[σ]` — i.e. "assuming the discharging
/// member's own invariant on entry, this recursive call establishes the target
/// member's invariant". The hypothesis is NOT carried as a field: the mint
/// derives it from `caller_member` against the member table, so a driver cannot
/// present one member's discharge under another member's (or an invented)
/// hypothesis.
pub struct InductiveStepProof<'a> {
    /// The SCC member whose body contains this recursive call (`C`). MUST name
    /// a member of the minted SCC — checked, not trusted.
    pub caller_member: String,
    pub call_site: SourceSpan,
    /// `P_target[actuals/formals]` — the producer (vcgen) owns σ.
    pub assumption_substituted: Formula,
    /// The exact preservation obligation the certificate is evidence for.
    pub vc: &'a VerificationCondition,
    /// Conjuncts admissible in `vc.formula` besides `¬P_target[σ]`: the
    /// caller's own path guards plus (at most) the caller's OWN inductive
    /// hypothesis `P_caller`. Any other member's invariant here is rejected.
    pub allowed_guards: Vec<Formula>,
    pub evidence: &'a trust_ir::ProofEvidence,
}

/// One SCC member's complete evidence bundle for
/// [`mint_inductive_caller_propagation_certificate`].
pub struct InductiveMemberProof<'a> {
    /// This member's def_path (`M`). The member table key.
    pub def_path: String,
    /// The obligation to flip (carries `V_M`).
    pub original_vc: &'a VerificationCondition,
    /// Its honest, isolated verdict — must be genuinely `Failed`.
    pub original_result: &'a VerificationResult,
    /// The inductive invariant `P_M` (gated to `M`'s parameter namespace).
    pub assumption: Formula,
    /// Formal parameter names/types for `M`, in declaration order.  These are
    /// the same producer-owned substitution inputs used by vcgen.  The mint
    /// uses them to reconstruct a fresh, one-member summary database containing
    /// exactly `P_M`; a dominance claim cannot supply a weaker precondition or
    /// unrelated result summaries.
    pub param_names: Vec<String>,
    pub param_types: Vec<trust_types::Ty>,
    /// `M`'s declared, gate-approved contract (`R_M`).
    pub gated_requires: Vec<Formula>,
    /// `V_M ∧ P_M` re-proved, + kernel evidence.
    pub strengthened: StrengthenedProof<'a>,
    /// Every EXTERNAL (non-SCC) caller the rustc oracle enumerated for `M`.
    pub enumerated_external_callers: Vec<String>,
    /// Per external call site: the UNCONDITIONAL discharge (`¬P_M[σ]`), with
    /// kernel evidence. Together with
    /// [`Self::dominated_external_callers`] must cover
    /// `enumerated_external_callers` exactly.
    pub base_case_proofs: Vec<CallerDischargeProof<'a>>,
    /// External callers that mint NO base-case VC because EVERY one of their
    /// call sites to `M` already establishes `P_M[σ]` by interval dominance —
    /// the exact condition under which trust-vcgen SUPPRESSES the obligation
    /// (F5). Suppression and absence are indistinguishable in a VC list, and
    /// they mean opposite things, so the caller's body is carried here and the
    /// mint RE-RUNS the predicate against a summary it reconstructs from this
    /// member's exact `def_path`, parameter metadata, and `assumption` (below).
    /// Nothing is taken on the producer's word.
    pub dominated_external_callers: Vec<DominatedCallerClaim<'a>>,
    /// Every INTRA-SCC caller (an SCC member whose body calls `M`) the rustc
    /// oracle enumerated.
    pub enumerated_scc_callers: Vec<String>,
    /// Per intra-SCC call site: the preservation discharge, with kernel
    /// evidence. Must cover `enumerated_scc_callers` exactly.
    pub inductive_step_proofs: Vec<InductiveStepProof<'a>>,
}

/// A base-case caller whose every call site to the member establishes the
/// member invariant by interval dominance. Carries the caller body the mint
/// needs to RE-DERIVE that verdict (`trust_vcgen::all_callsites_precondition_
/// dominated`) rather than trust the claim.  The member summary is deliberately
/// not carried here: the mint reconstructs it from `InductiveMemberProof`, so a
/// public claim cannot swap in a weaker `P` or forged auxiliary summaries.
pub struct DominatedCallerClaim<'a> {
    /// The caller's def_path — the name that must appear in the covered set.
    pub caller: String,
    /// The caller's extracted body, re-analyzed by the mint.
    pub caller_function: &'a trust_types::VerifiableFunction,
}

/// THE INDUCTIVE decision — the sealed-certificate constructor for a RECURSIVE
/// SCC (self- or mutual recursion), one token per member, all-or-nothing.
///
/// This is deliberately a SEPARATE mint from
/// [`mint_caller_propagation_certificate`]: that token's direct argument is
/// "every caller establishes `P`, *unconditionally*", and an intra-SCC
/// recursive call only establishes `P_target[σ]` **under the discharging
/// member's own hypothesis** — passing such a conditional discharge through the
/// direct mint would have the token vouch for a lemma it does not witness (the
/// exact over-claim class the 72ada1163c audit stopped). Here the conditional
/// discharges are admitted ONLY inside a checked induction over the whole SCC.
///
/// Every check is fail-closed and any member's failure rejects the WHOLE SCC
/// (the cycle is only jointly inductive if every member holds up its lemma):
///
///  1. member def_paths are pairwise distinct (unambiguous invariant lookup);
///  2. per member: the original obligation genuinely `Failed` (necessity);
///  3. per member: `P_M` is CONNECTED to `V_M` (free vars a non-empty subset);
///  4. per member: the strengthened VC really is `V_M ∧ P_M` (+ at most `R_M`)
///     at the same kind/location, and its certificate REPLAYS through the clean
///     kernel ([`trust_certify::replay_vc_evidence`]);
///  5. per member: the BASE-CASE discharges cover EXACTLY the enumerated
///     external caller set; no enumerated external caller is an SCC member; no
///     base-case guard equals ANY member invariant (the base case must be
///     unconditional); each obligation is structurally `¬P_M[σ]` (+ allowed
///     guards) and its certificate REPLAYS;
///  6. per member: the INDUCTIVE-STEP discharges cover EXACTLY the enumerated
///     intra-SCC caller set; each names a real SCC member `C`; any guard equal
///     to a member invariant is exactly `C`'s own `P_C` (the hypothesis a
///     recursive call is entitled to — never another member's, never the
///     target's); each obligation is structurally `¬P_M[σ]` (+ allowed guards)
///     and its certificate REPLAYS;
///  7. per member: at least one obligation constrains it (an unconstrained
///     member's `P` is established nowhere — reject, fail-closed);
///  8. across the SCC: at least one base-case discharge exists (the induction
///     is grounded at a real external entry).
///
/// SOUNDNESS ARGUMENT (the induction the tokens witness). Let the SCC be
/// `{M_1..M_k}` with invariants `P_i` and violations `V_i`, each `V_i ∧ P_i`
/// kernel-UNSAT (4). CLAIM: on every real execution, `P_i` holds at every entry
/// of `M_i`; hence (by 4) no `V_i` ever fires, and attributing `Proved` to each
/// `V_i` is sound. PROOF by strong induction on the number of SCC entries the
/// execution has performed. Consider the n-th dynamic entry, into `M_i`, from
/// immediate caller `C`:
///
///  * `C` outside the SCC (base case): the driver's oracle judged every
///    external entry of `M_i` enumerable (the same closed-world judgment the
///    direct mint trusts), (5) demands a discharge for exactly that set, and
///    the replayed UNSAT of `guards ∧ ¬P_i[σ]` shows the call establishes
///    `P_i` given only `C`'s own path guards — which hold on the executed path.
///  * `C = M_j` inside the SCC (inductive step): the entry to `M_j` currently
///    on the stack was an earlier SCC entry (m < n), so by the induction
///    hypothesis `P_j` held at it. (6) demands a discharge for exactly the
///    enumerated intra-SCC caller set, its guard hygiene ensures the only
///    invariant assumed is `P_j` itself, and the replayed UNSAT of
///    `P_j ∧ guards ∧ ¬P_i[σ]` shows the call establishes `P_i`.
///
/// The first SCC entry of any execution is necessarily external, so the
/// induction is grounded per-execution by the base case; (8) additionally
/// refuses an SCC no execution can enter at all rather than mint vacuous
/// tokens. The non-kernel trusted inputs are identical to the direct mint's:
/// the rustc oracle's caller enumeration/closed-world judgment and vcgen's
/// substitution σ and path guards — both already in the trusted base that
/// generated each `V_i` itself.
///
/// Returns one sealed token per member, in input order.
pub fn mint_inductive_caller_propagation_certificate(
    members: &[InductiveMemberProof<'_>],
) -> Result<Vec<SealedCallerPropagationCertificate>, R1Reject> {
    if members.is_empty() {
        return Err(R1Reject::NoCallers);
    }
    // (1) The member table: def_path -> its invariant. Pairwise distinct.
    let mut invariant_of: FxHashMap<&str, &Formula> = FxHashMap::default();
    for m in members {
        if invariant_of.insert(m.def_path.as_str(), &m.assumption).is_some() {
            return Err(R1Reject::InductiveMemberDuplicate { member: m.def_path.clone() });
        }
    }

    // Exact set equality (dedup by name), shared by (5) and (6).
    let exact_caller_set = |proofs: &[&str], enumerated: &[String]| -> Result<(), R1Reject> {
        let mut proved: Vec<&str> = proofs.to_vec();
        proved.sort_unstable();
        proved.dedup();
        let mut expected: Vec<&str> = enumerated.iter().map(String::as_str).collect();
        expected.sort_unstable();
        expected.dedup();
        if proved != expected {
            return Err(R1Reject::CallerSetMismatch {
                expected: expected.iter().map(|s| (*s).to_string()).collect(),
                covered: proved.iter().map(|s| (*s).to_string()).collect(),
            });
        }
        Ok(())
    };

    let mut total_external_discharges = 0usize;
    let mut certs = Vec::with_capacity(members.len());
    for m in members {
        // (2) NECESSITY — as in the direct mint.
        if !m.original_result.is_failed() {
            return Err(R1Reject::NotNecessary);
        }
        // (3) CONNECTEDNESS — as in the direct mint.
        let avars = m.assumption.free_variables();
        if avars.is_empty() || !avars.is_subset(&m.original_vc.formula.free_variables()) {
            return Err(R1Reject::Disconnected);
        }
        // (4) THE STRENGTHENED VC IS THE RIGHT ONE, AND ITS PROOF REPLAYS —
        //     identical criteria to the direct mint's checks (4) and (5).
        if m.strengthened.vc.kind.description() != m.original_vc.kind.description()
            || m.strengthened.vc.location != m.original_vc.location
        {
            return Err(R1Reject::StrengthenedFormulaMismatch);
        }
        {
            let s_conj = conjuncts_of(&m.strengthened.vc.formula);
            let v_conj = conjuncts_of(&m.original_vc.formula);
            if !s_conj.contains(&m.assumption) {
                return Err(R1Reject::StrengthenedFormulaMismatch);
            }
            if !v_conj.iter().all(|c| s_conj.contains(c)) {
                return Err(R1Reject::StrengthenedFormulaMismatch);
            }
            if !s_conj
                .iter()
                .all(|c| *c == m.assumption || v_conj.contains(c) || m.gated_requires.contains(c))
            {
                return Err(R1Reject::StrengthenedFormulaMismatch);
            }
        }
        if !trust_certify::replay_vc_evidence(m.strengthened.vc, m.strengthened.evidence) {
            return Err(R1Reject::StrengthenedNotReplayed);
        }

        // (5) BASE CASE — every enumerated EXTERNAL caller, exactly, each
        //     unconditional, each replayed.
        for c in &m.enumerated_external_callers {
            if invariant_of.contains_key(c.as_str()) {
                return Err(R1Reject::InductiveCallerNotMember {
                    member: m.def_path.clone(),
                    caller: c.clone(),
                });
            }
        }
        // RE-DERIVE every claimed dominance here. The producer's claim is not
        // evidence; the predicate is re-run on the caller body against a FRESH
        // one-member summary DB containing exactly this member's P.  In
        // particular, no public `FunctionSummary::result_range`, extracted body,
        // weaker precondition, or unrelated summary can influence the replay.
        // A claim that does not reproduce is dropped, so it cannot contribute
        // to coverage and the exact-set check below rejects the whole harvest.
        let mut dominance_db = trust_vcgen::SummaryDatabase::new();
        dominance_db.insert(
            trust_vcgen::FunctionSummary::new(m.def_path.clone())
                .with_param_names(m.param_names.clone())
                .with_param_types(m.param_types.clone())
                .with_precondition(m.assumption.clone()),
        );
        let mut dominated: Vec<&str> = Vec::new();
        for claim in &m.dominated_external_callers {
            if claim.caller_function.def_path != claim.caller {
                return Err(R1Reject::DominatedCallerIdentityMismatch {
                    claimed: claim.caller.clone(),
                    actual: claim.caller_function.def_path.clone(),
                });
            }
            if invariant_of.contains_key(claim.caller.as_str()) {
                return Err(R1Reject::InductiveCallerNotMember {
                    member: m.def_path.clone(),
                    caller: claim.caller.clone(),
                });
            }
            if trust_vcgen::all_callsites_precondition_dominated(
                claim.caller_function,
                &dominance_db,
                &m.def_path,
            ) {
                dominated.push(claim.caller.as_str());
            }
        }
        let mut covered: Vec<&str> = m.base_case_proofs.iter().map(|o| o.caller.as_str()).collect();
        covered.extend(dominated.iter().copied());
        exact_caller_set(&covered, &m.enumerated_external_callers)?;
        let mut caller_sites = Vec::new();
        for o in &m.base_case_proofs {
            // UNCONDITIONAL: a member invariant among the guards would make the
            // base case assume the very induction it must ground. (A genuine
            // external guard that merely coincides textually with some `P` is
            // rejected too — fail-closed, never unsound.)
            if o.allowed_guards.iter().any(|g| invariant_of.values().any(|p| *p == g)) {
                return Err(R1Reject::InductiveForeignHypothesis {
                    member: m.def_path.clone(),
                    caller: o.caller.clone(),
                });
            }
            if !is_admissible_caller_discharge(
                &o.vc.formula,
                &o.assumption_substituted,
                &o.allowed_guards,
            ) {
                return Err(R1Reject::CallerFormulaMismatch {
                    caller: o.caller.clone(),
                    call_site: o.call_site.clone(),
                });
            }
            if !trust_certify::replay_vc_evidence(o.vc, o.evidence) {
                return Err(R1Reject::CallerNotReplayed {
                    caller: o.caller.clone(),
                    call_site: o.call_site.clone(),
                });
            }
            caller_sites.push(SealedVcIdentity::of(o.vc));
        }
        // A dominance-discharged external caller (re-derived above) is a REAL
        // external entry that grounds the induction just as an unconditional
        // ¬P[σ] discharge does — at such a caller the member is invoked with an
        // argument for which P holds outright. Count both toward grounding.
        total_external_discharges += m.base_case_proofs.len() + dominated.len();

        // (6) INDUCTIVE STEP — every enumerated INTRA-SCC caller, exactly, each
        //     under (at most) its OWN hypothesis, each replayed.
        for c in &m.enumerated_scc_callers {
            if !invariant_of.contains_key(c.as_str()) {
                return Err(R1Reject::InductiveCallerNotMember {
                    member: m.def_path.clone(),
                    caller: c.clone(),
                });
            }
        }
        exact_caller_set(
            &m.inductive_step_proofs.iter().map(|o| o.caller_member.as_str()).collect::<Vec<_>>(),
            &m.enumerated_scc_callers,
        )?;
        for o in &m.inductive_step_proofs {
            let Some(&own_p) = invariant_of.get(o.caller_member.as_str()) else {
                return Err(R1Reject::InductiveCallerNotMember {
                    member: m.def_path.clone(),
                    caller: o.caller_member.clone(),
                });
            };
            // HYPOTHESIS HYGIENE — by VALUE, not provenance: any guard equal to
            // a member invariant must EQUAL the discharging caller's own `P` —
            // the one thing a recursive call is entitled to assume (established
            // at `C`'s own entry by this very induction). Value comparison is
            // load-bearing for completeness: a SYMMETRIC SCC infers textually
            // IDENTICAL invariants for its members (mutual `ping`/`pong` both
            // `i < 8`), so a per-provenance check would mistake the spliced
            // own-hypothesis for another member's and refuse the whole SCC. A
            // formula equal to `P_C` IS `P_C` — formulas are syntax, and what
            // is assumed is exactly what `C`'s entry establishes. Soundness is
            // unaffected: any guard matching a member invariant while differing
            // from `C`'s own still rejects as unearned.
            if o.allowed_guards
                .iter()
                .any(|g| *g != *own_p && invariant_of.values().any(|p| **p == *g))
            {
                return Err(R1Reject::InductiveForeignHypothesis {
                    member: m.def_path.clone(),
                    caller: o.caller_member.clone(),
                });
            }
            if !is_admissible_caller_discharge(
                &o.vc.formula,
                &o.assumption_substituted,
                &o.allowed_guards,
            ) {
                return Err(R1Reject::CallerFormulaMismatch {
                    caller: o.caller_member.clone(),
                    call_site: o.call_site.clone(),
                });
            }
            if !trust_certify::replay_vc_evidence(o.vc, o.evidence) {
                return Err(R1Reject::CallerNotReplayed {
                    caller: o.caller_member.clone(),
                    call_site: o.call_site.clone(),
                });
            }
            caller_sites.push(SealedVcIdentity::of(o.vc));
        }

        // (7) CONSTRAINEDNESS — a member no call reaches has its `P`
        //     established nowhere; refuse rather than mint a vacuous token.
        if m.base_case_proofs.is_empty()
            && dominated.is_empty()
            && m.inductive_step_proofs.is_empty()
        {
            return Err(R1Reject::InductiveMemberUnconstrained { member: m.def_path.clone() });
        }

        let mut covered_callers: Vec<String> = m
            .enumerated_external_callers
            .iter()
            .chain(m.enumerated_scc_callers.iter())
            .cloned()
            .collect();
        covered_callers.sort();
        covered_callers.dedup();
        certs.push(SealedCallerPropagationCertificate {
            discharge: SealedVcIdentity::of(m.original_vc),
            strengthened: SealedVcIdentity::of(m.strengthened.vc),
            caller_sites,
            covered_callers,
            assumption: m.assumption.clone(),
            provenance: SealedCertificateProvenance::InductiveSccPropagation,
        });
    }

    // (8) GROUNDING — at least one real external entry across the whole SCC.
    if total_external_discharges == 0 {
        return Err(R1Reject::InductiveUngrounded);
    }
    Ok(certs)
}

#[cfg(test)]
mod tests {
    use trust_types::call_graph::{CallGraphEdge, CallGraphNode};
    use trust_types::{ProofStrength, parse_spec_expr};

    use super::*;

    fn certified() -> VerificationResult {
        VerificationResult::Proved {
            solver: "ay".into(),
            time_ms: 1,
            strength: ProofStrength::smt_unsat_certified(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        }
    }
    fn unvalidated() -> VerificationResult {
        VerificationResult::Proved {
            solver: "ay".into(),
            time_ms: 1,
            strength: ProofStrength::smt_unsat_unvalidated(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        }
    }
    fn failed() -> VerificationResult {
        VerificationResult::Failed { solver: "ay".into(), time_ms: 1, counterexample: None }
    }
    fn fx(s: &str) -> Formula {
        parse_spec_expr(s).expect("parses")
    }
    fn not(g: Formula) -> Formula {
        Formula::Not(Box::new(g))
    }

    // P over F's params; V over the same — connected.
    fn p() -> Formula {
        fx("n < 100")
    }
    fn v() -> Formula {
        fx("n > 50")
    }
    // In a caller, the actual for `n` is `x`, so P[σ] = "x < 100".
    fn p_sub() -> Formula {
        fx("x < 100")
    }

    fn node(dp: &str) -> CallGraphNode {
        CallGraphNode {
            def_path: dp.into(),
            name: dp.into(),
            is_public: false,
            is_entry_point: false,
            span: SourceSpan::default(),
        }
    }
    fn edge(c: &str, e: &str) -> CallGraphEdge {
        CallGraphEdge { caller: c.into(), callee: e.into(), call_site: SourceSpan::default() }
    }
    #[test]
    fn caller_discharge_accepts_bare_and_guarded() {
        assert!(is_admissible_caller_discharge(&not(p_sub()), &p_sub(), &[]));
        let guard = fx("x > 0");
        let with_guard = Formula::And(vec![guard.clone(), not(p_sub())]);
        assert!(is_admissible_caller_discharge(&with_guard, &p_sub(), &[guard]));
    }
    #[test]
    fn caller_discharge_rejects_free_form_and_wrong_negation() {
        // extra conjunct not in the allowlist
        let sneaky = Formula::And(vec![fx("x > 0"), not(p_sub())]);
        assert!(!is_admissible_caller_discharge(&sneaky, &p_sub(), &[]));
        // negates a DIFFERENT predicate than P[σ]
        let wrong = not(fx("x < 999"));
        assert!(!is_admissible_caller_discharge(&wrong, &p_sub(), &[]));
    }

    // ---- reverse graph / coverage ----
    #[test]
    fn reverse_graph_and_callers() {
        let mut g = CallGraph::new();
        for n in ["a", "b", "fdef"] {
            g.add_node(node(n));
        }
        g.add_edge(edge("a", "fdef"));
        g.add_edge(edge("b", "fdef"));
        let rev = reverse_call_graph(&g);
        let mut cs = rev["fdef"].clone();
        cs.sort();
        assert_eq!(cs, vec!["a".to_string(), "b".to_string()]);
        assert_eq!(callers_of(&g, "fdef").len(), 2);
    }
    #[test]
    fn coverage_total_vs_incomplete() {
        let rec = FxHashSet::default();
        assert_eq!(
            classify_coverage("fdef", &rec, &CoverageSignals::default()),
            CallerCoverage::Total
        );
        let sig = CoverageSignals { is_public: true, ..Default::default() };
        assert!(matches!(classify_coverage("fdef", &rec, &sig), CallerCoverage::Incomplete(_)));
        let sig = CoverageSignals { address_taken: true, ..Default::default() };
        assert!(matches!(classify_coverage("fdef", &rec, &sig), CallerCoverage::Incomplete(_)));
    }

    /// A poisoned crate-wide scan must reject with its OWN reason. It used to
    /// arrive folded into `is_public`, which classified it as
    /// `ExternallyReachable` — a claim that is false for every cause of the
    /// poison (an unscannable body or a `global_asm!` item says nothing about
    /// F's visibility), though no consumer ever rendered it: the real defect was
    /// that the cause was dropped unread, leaving the crate-level rejection
    /// unexplained. This test doubles as the pin on `classify_coverage`'s
    /// `ScanIncomplete` push: delete that loop and the destructuring below
    /// panics on `Total`.
    #[test]
    fn scan_incomplete_rejects_without_claiming_external_reachability() {
        let rec = FxHashSet::default();
        let sig = CoverageSignals {
            scan_incomplete: vec!["`demo::{{global_asm}}` is a `global_asm!` item".to_string()],
            ..Default::default()
        };
        let CallerCoverage::Incomplete(gaps) = classify_coverage("fdef", &rec, &sig) else {
            panic!("a poisoned scan must never classify as Total");
        };
        assert_eq!(
            gaps,
            vec![CoverageGap::ScanIncomplete {
                reason: "`demo::{{global_asm}}` is a `global_asm!` item".to_string()
            }],
            "the scan reason must survive; `ExternallyReachable` would be a false reason"
        );
        assert!(!gaps.contains(&CoverageGap::ExternallyReachable));
    }

    /// END-TO-END PIN for the narrowed `is_public`: with the scan poison as the
    /// ONLY hazard (`is_public` and `address_taken` both false — exactly the
    /// world after the poison stopped being folded into `is_public`), the
    /// signals → `classify_coverage` → `mint_caller_propagation_certificate`
    /// pipeline must refuse to flip even on perfect kernel-replayed proofs.
    /// This FAILS if the poison ever stops blocking flips through its own
    /// `scan_incomplete` channel: were `classify_coverage` to ignore the field,
    /// coverage would classify `Total` and the mint below would succeed.
    #[test]
    fn scan_poison_alone_blocks_the_mint_through_classification() {
        let reason = "the elaborated MIR of `demo::helper` was already stolen".to_string();
        let sig = CoverageSignals::new(false, false, vec![], vec![reason.clone()]);
        let rec = FxHashSet::default();
        let coverage = classify_coverage("helper", &rec, &sig);
        let (v, s) = (v_vc(), s_vc());
        let s_ev = evidence_for(&s);
        let c_vc = caller_vc("main");
        let c_ev = evidence_for(&c_vc);
        assert_eq!(
            mint_caller_propagation_certificate(
                &v,
                &failed(),
                &p_r1(),
                &[],
                &StrengthenedProof { vc: &s, evidence: &s_ev },
                &coverage,
                &["main".to_string()],
                &[caller_proof("main", &c_vc, &c_ev)],
            )
            .map(|_| ()),
            Err(R1Reject::CoverageIncomplete(vec![CoverageGap::ScanIncomplete { reason }]))
        );
    }

    /// The reasons must not be swallowed when F ALSO has a real per-function gap:
    /// both causes are true and both are reported, crate-level cause first.
    #[test]
    fn scan_incomplete_accumulates_with_per_function_gaps() {
        let rec = FxHashSet::default();
        let sig = CoverageSignals {
            is_public: true,
            address_taken: true,
            scan_incomplete: vec!["`demo::{{global_asm}}` is a `global_asm!` item".to_string()],
            ..Default::default()
        };
        let CallerCoverage::Incomplete(gaps) = classify_coverage("fdef", &rec, &sig) else {
            panic!("a poisoned scan must never classify as Total");
        };
        assert_eq!(
            gaps,
            vec![
                CoverageGap::ScanIncomplete {
                    reason: "`demo::{{global_asm}}` is a `global_asm!` item".to_string()
                },
                CoverageGap::ExternallyReachable,
                CoverageGap::IndirectCall { detail: "address-taken (fn-ptr/dyn)".into() },
            ]
        );
    }

    // ---- the decision (sealed certificate + real kernel replay) ----
    //
    // These tests mint GENUINE clean-kernel certificates via `trust_certify` —
    // no mocks, no fabricated evidence. That is the point: the sealed token can
    // only be produced from evidence that actually replays, so a test that
    // cannot produce real evidence cannot produce a token either.

    /// F = `fn helper(x, divisor) { x / divisor }` after MIR lowering: the
    /// div-by-zero violation `_4 = divisor ∧ _5 ⇔ (_4 == 0) ∧ _5`. SAT in
    /// isolation (divisor may be 0) — this is the obligation R1 flips.
    fn v_vc() -> VerificationCondition {
        let divisor = || Formula::Var("divisor".to_string(), trust_types::Sort::Int);
        let four = || Formula::Var("_4".to_string(), trust_types::Sort::Int);
        let five = || Formula::Var("_5".to_string(), trust_types::Sort::Bool);
        VerificationCondition {
            kind: trust_types::VcKind::DivisionByZero,
            function: "helper".into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![
                Formula::Eq(Box::new(four()), Box::new(divisor())),
                Formula::Eq(
                    Box::new(five()),
                    Box::new(Formula::Eq(Box::new(four()), Box::new(Formula::Int(0)))),
                ),
                five(),
            ]),
            contract_metadata: None,
            obligation: None,
        }
    }

    /// The inferred precondition P = `divisor != 0`, over F's parameter namespace.
    fn p_r1() -> Formula {
        Formula::Not(Box::new(Formula::Eq(
            Box::new(Formula::Var("divisor".to_string(), trust_types::Sort::Int)),
            Box::new(Formula::Int(0)),
        )))
    }

    /// The strengthened obligation `V ∧ P` — UNSAT, and kernel-certifiable.
    fn s_vc() -> VerificationCondition {
        let mut vc = v_vc();
        let mut conj = conjuncts_of(&vc.formula);
        conj.insert(0, p_r1());
        vc.formula = Formula::And(conj);
        vc
    }

    /// A call site `helper(10, 5)`: the discharge obligation `¬P[σ]` = `¬¬(5 = 0)`,
    /// UNSAT (5 != 0 really does hold), so it kernel-certifies.
    fn caller_vc(caller: &str) -> VerificationCondition {
        VerificationCondition {
            kind: trust_types::VcKind::Precondition { callee: "helper".into() },
            function: caller.into(),
            location: SourceSpan::default(),
            formula: not(p_sigma()),
            contract_metadata: None,
            obligation: None,
        }
    }

    /// `P[σ]` at the site `helper(10, 5)`: `5 != 0`.
    fn p_sigma() -> Formula {
        Formula::Not(Box::new(Formula::Eq(Box::new(Formula::Int(5)), Box::new(Formula::Int(0)))))
    }

    fn evidence_for(vc: &VerificationCondition) -> trust_ir::ProofEvidence {
        trust_certify::certify_vc(vc).unwrap_or_else(|| panic!("{:?} must kernel-certify", vc.kind))
    }

    fn caller_proof<'a>(
        caller: &str,
        vc: &'a VerificationCondition,
        evidence: &'a trust_ir::ProofEvidence,
    ) -> CallerDischargeProof<'a> {
        CallerDischargeProof {
            caller: caller.into(),
            call_site: SourceSpan::default(),
            assumption_substituted: p_sigma(),
            vc,
            allowed_guards: vec![],
            evidence,
        }
    }

    /// POSITIVE CONTROL — the `flip_caller_covered` shape mints a sealed token:
    /// the strengthened VC and the sole call site both carry certificates that
    /// REPLAY through the clean kernel.
    #[test]
    fn sealed_certificate_mints_on_real_replayed_kernel_evidence() {
        let (v, s) = (v_vc(), s_vc());
        let s_ev = evidence_for(&s);
        let c_vc = caller_vc("main");
        let c_ev = evidence_for(&c_vc);
        let cert = mint_caller_propagation_certificate(
            &v,
            &failed(),
            &p_r1(),
            &[],
            &StrengthenedProof { vc: &s, evidence: &s_ev },
            &CallerCoverage::Total,
            &["main".to_string()],
            &[caller_proof("main", &c_vc, &c_ev)],
        )
        .expect("real replayed evidence must mint a sealed certificate");

        // The token binds BOTH obligations, and authorizes exactly V's operation.
        assert_eq!(cert.provenance(), SealedCertificateProvenance::DirectCallerPropagation);
        assert_eq!(cert.discharge_identity(), &SealedVcIdentity::of(&v));
        assert_eq!(cert.strengthened_identity(), &SealedVcIdentity::of(&s));
        assert_ne!(cert.discharge_identity().digest(), cert.strengthened_identity().digest());
        assert_eq!(cert.caller_site_count(), 1);
        assert_eq!(cert.covered_callers(), ["main".to_string()]);
        assert!(cert.authorizes_operation(
            &v.kind.description(),
            &v.location.file,
            v.location.line_start,
            v.location.col_start
        ));
        assert!(
            !cert.authorizes_operation("Division by zero", "other.rs", 999, 1),
            "the token must not authorize an unrelated operation"
        );
        assert!(matches!(
            cert.attributed_verdict(),
            VerificationResult::Proved { strength, .. }
                if strength == ProofStrength::deductive()
        ));
    }

    /// WITNESS-SWAP — a REAL certificate for a DIFFERENT obligation is not
    /// evidence for this one. The kernel replay is identity-bound, so presenting
    /// the call site's (genuine!) certificate as the strengthened proof fails.
    /// This is the exact forgery class the public `Certified` label could not
    /// detect: both labels say "Proved".
    #[test]
    fn mint_rejects_a_real_certificate_for_the_wrong_obligation() {
        let (v, s) = (v_vc(), s_vc());
        let c_vc = caller_vc("main");
        let c_ev = evidence_for(&c_vc); // genuine — but for the CALL SITE
        let s_ev = evidence_for(&s);
        assert_eq!(
            mint_caller_propagation_certificate(
                &v,
                &failed(),
                &p_r1(),
                &[],
                &StrengthenedProof { vc: &s, evidence: &c_ev }, // swapped!
                &CallerCoverage::Total,
                &["main".to_string()],
                &[caller_proof("main", &c_vc, &c_ev)],
            )
            .map(|_| ()),
            Err(R1Reject::StrengthenedNotReplayed)
        );
        // ... and symmetrically at the call site.
        assert_eq!(
            mint_caller_propagation_certificate(
                &v,
                &failed(),
                &p_r1(),
                &[],
                &StrengthenedProof { vc: &s, evidence: &s_ev },
                &CallerCoverage::Total,
                &["main".to_string()],
                &[caller_proof("main", &c_vc, &s_ev)], // swapped!
            )
            .map(|_| ()),
            Err(R1Reject::CallerNotReplayed {
                caller: "main".into(),
                call_site: SourceSpan::default()
            })
        );
    }

    /// SOUNDNESS CONTROL (`reject_unconstrained_caller`) — if ONE enumerated
    /// caller is missing from the discharge list, refuse. Assuming P at an entry
    /// that never establishes it is the catastrophic case. The pre-audit gate
    /// iterated only the list it was handed and never cross-checked the call
    /// graph, so a dropped caller would have flipped unsoundly.
    #[test]
    fn mint_rejects_a_dropped_caller() {
        let (v, s) = (v_vc(), s_vc());
        let s_ev = evidence_for(&s);
        let c_vc = caller_vc("caller_ok");
        let c_ev = evidence_for(&c_vc);
        assert_eq!(
            mint_caller_propagation_certificate(
                &v,
                &failed(),
                &p_r1(),
                &[],
                &StrengthenedProof { vc: &s, evidence: &s_ev },
                &CallerCoverage::Total,
                // The oracle found TWO callers; only one discharged.
                &["caller_ok".to_string(), "caller_bad".to_string()],
                &[caller_proof("caller_ok", &c_vc, &c_ev)],
            )
            .map(|_| ()),
            Err(R1Reject::CallerSetMismatch {
                expected: vec!["caller_bad".into(), "caller_ok".into()],
                covered: vec!["caller_ok".into()],
            })
        );
    }

    /// SOUNDNESS CONTROL (`reject_public` / `reject_no_mangle` /
    /// `reject_address_taken`) — incomplete coverage refuses regardless of how
    /// good the proofs are. An externally-reachable F can be entered with any
    /// argument, so no set of in-crate call sites establishes P.
    #[test]
    fn mint_rejects_incomplete_coverage_even_with_perfect_proofs() {
        let (v, s) = (v_vc(), s_vc());
        let s_ev = evidence_for(&s);
        let c_vc = caller_vc("main");
        let c_ev = evidence_for(&c_vc);
        for gap in [
            CoverageGap::ExternallyReachable,
            CoverageGap::IndirectCall { detail: "address-taken (fn-ptr/dyn)".into() },
            CoverageGap::Recursive,
            // The crate-wide scan poison rejects exactly as hard as the per-function
            // gaps do; naming its real cause never softened the decision.
            CoverageGap::ScanIncomplete { reason: "`demo::{{global_asm}}` item".into() },
        ] {
            assert_eq!(
                mint_caller_propagation_certificate(
                    &v,
                    &failed(),
                    &p_r1(),
                    &[],
                    &StrengthenedProof { vc: &s, evidence: &s_ev },
                    &CallerCoverage::Incomplete(vec![gap.clone()]),
                    &["main".to_string()],
                    &[caller_proof("main", &c_vc, &c_ev)],
                )
                .map(|_| ()),
                Err(R1Reject::CoverageIncomplete(vec![gap]))
            );
        }
    }

    /// A genuinely-proved obligation that is NOT `V ∧ P` proves something else.
    /// Here the "strengthened" VC drops a conjunct of V, so its (real!) proof
    /// does not establish that F is safe under P.
    #[test]
    fn mint_rejects_a_strengthened_proof_of_a_different_formula() {
        let v = v_vc();
        let mut s = s_vc();
        // Drop V's `_5` assertion — a strictly weaker obligation.
        let kept: Vec<Formula> = conjuncts_of(&s.formula).into_iter().take(3).collect();
        s.formula = Formula::And(kept);
        let s_ev = trust_certify::certify_vc(&s);
        let c_vc = caller_vc("main");
        let c_ev = evidence_for(&c_vc);
        // Whether or not the mangled VC certifies, the STRUCTURAL check must
        // reject it before any evidence is even consulted.
        let dummy = s_ev.unwrap_or_else(|| evidence_for(&c_vc));
        assert_eq!(
            mint_caller_propagation_certificate(
                &v,
                &failed(),
                &p_r1(),
                &[],
                &StrengthenedProof { vc: &s, evidence: &dummy },
                &CallerCoverage::Total,
                &["main".to_string()],
                &[caller_proof("main", &c_vc, &c_ev)],
            )
            .map(|_| ()),
            Err(R1Reject::StrengthenedFormulaMismatch)
        );
    }

    /// NECESSITY — an obligation that did not genuinely fail has no
    /// counterexample for P to rule out; flipping it would over-claim.
    #[test]
    fn mint_rejects_a_non_failed_original() {
        let (v, s) = (v_vc(), s_vc());
        let s_ev = evidence_for(&s);
        let c_vc = caller_vc("main");
        let c_ev = evidence_for(&c_vc);
        let unknown =
            VerificationResult::Unknown { solver: "ay".into(), time_ms: 1, reason: String::new() };
        assert_eq!(
            mint_caller_propagation_certificate(
                &v,
                &unknown,
                &p_r1(),
                &[],
                &StrengthenedProof { vc: &s, evidence: &s_ev },
                &CallerCoverage::Total,
                &["main".to_string()],
                &[caller_proof("main", &c_vc, &c_ev)],
            )
            .map(|_| ()),
            Err(R1Reject::NotNecessary)
        );
    }

    /// VACUITY (#540) — a P that shares no symbol with V does not constrain the
    /// program, so it cannot discharge anything.
    #[test]
    fn mint_rejects_a_disconnected_assumption() {
        let (v, s) = (v_vc(), s_vc());
        let s_ev = evidence_for(&s);
        let c_vc = caller_vc("main");
        let c_ev = evidence_for(&c_vc);
        let disconnected = Formula::Not(Box::new(Formula::Eq(
            Box::new(Formula::Var("__precond_0".to_string(), trust_types::Sort::Int)),
            Box::new(Formula::Int(0)),
        )));
        assert_eq!(
            mint_caller_propagation_certificate(
                &v,
                &failed(),
                &disconnected,
                &[],
                &StrengthenedProof { vc: &s, evidence: &s_ev },
                &CallerCoverage::Total,
                &["main".to_string()],
                &[caller_proof("main", &c_vc, &c_ev)],
            )
            .map(|_| ()),
            Err(R1Reject::Disconnected)
        );
    }

    /// A call-site obligation that is not `¬P[σ]` (+ allowed guards) proves
    /// something other than "this caller establishes P".
    #[test]
    fn mint_rejects_a_caller_obligation_of_the_wrong_shape() {
        let (v, s) = (v_vc(), s_vc());
        let s_ev = evidence_for(&s);
        let c_vc = caller_vc("main");
        let c_ev = evidence_for(&c_vc);
        let mut bad = caller_proof("main", &c_vc, &c_ev);
        // The certificate is real and replays, but it is evidence for `¬(5 = 0)`,
        // not for the negation of the P[σ] we claim.
        bad.assumption_substituted = fx("x < 100");
        assert_eq!(
            mint_caller_propagation_certificate(
                &v,
                &failed(),
                &p_r1(),
                &[],
                &StrengthenedProof { vc: &s, evidence: &s_ev },
                &CallerCoverage::Total,
                &["main".to_string()],
                &[bad],
            )
            .map(|_| ()),
            Err(R1Reject::CallerFormulaMismatch {
                caller: "main".into(),
                call_site: SourceSpan::default()
            })
        );
    }

    /// No callers at all ⇒ P is established nowhere.
    #[test]
    fn mint_rejects_zero_callers() {
        let (v, s) = (v_vc(), s_vc());
        let s_ev = evidence_for(&s);
        assert_eq!(
            mint_caller_propagation_certificate(
                &v,
                &failed(),
                &p_r1(),
                &[],
                &StrengthenedProof { vc: &s, evidence: &s_ev },
                &CallerCoverage::Total,
                &[],
                &[],
            )
            .map(|_| ()),
            Err(R1Reject::NoCallers)
        );
    }

    // ---- the INDUCTIVE decision (sealed SCC certificates + real kernel replay) ----
    //
    // Model: the self-recursive SCC `{helper}` where `helper(x, divisor)` divides
    // and recurses passing `divisor` through unchanged, entered once from `main`
    // as `helper(10, 5)`. P = `divisor != 0`.

    /// The intra-SCC preservation obligation for the self-loop: the recursive
    /// call passes `divisor` through, so `P[σ] = P` and the obligation is
    /// `P ∧ ¬P[σ]` — UNSAT, kernel-certifiable (double-negation elimination +
    /// direct disequality contradiction).
    fn ind_vc() -> VerificationCondition {
        VerificationCondition {
            kind: trust_types::VcKind::Precondition { callee: "helper".into() },
            function: "helper".into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![p_r1(), not(p_r1())]),
            contract_metadata: None,
            obligation: None,
        }
    }

    fn ind_proof<'a>(
        vc: &'a VerificationCondition,
        evidence: &'a trust_ir::ProofEvidence,
    ) -> InductiveStepProof<'a> {
        InductiveStepProof {
            caller_member: "helper".into(),
            call_site: SourceSpan::default(),
            assumption_substituted: p_r1(),
            vc,
            allowed_guards: vec![p_r1()], // the caller's OWN hypothesis
            evidence,
        }
    }

    /// A one-site caller whose literal actual establishes the integer interval
    /// precondition used by F5.  Keeping this body synthetic and tiny makes the
    /// sealed-mint test exercise the same public dominance predicate as rustc,
    /// without relying on a producer claim or mocked proof label.
    fn dominated_caller(def_path: &str) -> trust_types::VerifiableFunction {
        trust_types::VerifiableFunction {
            name: def_path.into(),
            def_path: def_path.into(),
            span: SourceSpan::default(),
            body: trust_types::VerifiableBody {
                locals: vec![trust_types::LocalDecl {
                    index: 0,
                    ty: trust_types::Ty::unit_ty(),
                    name: None,
                }],
                blocks: vec![trust_types::BasicBlock {
                    id: trust_types::BlockId(0),
                    stmts: vec![],
                    terminator: trust_types::Terminator::Call {
                        func: "helper".into(),
                        args: vec![trust_types::Operand::Constant(trust_types::ConstValue::Uint(
                            5, 32,
                        ))],
                        dest: trust_types::Place::local(0),
                        target: None,
                        span: SourceSpan::default(),
                        atomic: None,
                        is_foreign: false,
                        is_unsafe_sig: false,
                        unwind: trust_types::UnwindEdge::Unreachable,
                    },
                }],
                arg_count: 0,
                return_ty: trust_types::Ty::unit_ty(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn dominance_p() -> Formula {
        Formula::Ge(
            Box::new(Formula::Var("divisor".into(), trust_types::Sort::Int)),
            Box::new(Formula::Int(0)),
        )
    }

    fn dominance_vc() -> VerificationCondition {
        VerificationCondition {
            kind: trust_types::VcKind::DivisionByZero,
            function: "helper".into(),
            location: SourceSpan::default(),
            formula: Formula::Lt(
                Box::new(Formula::Var("divisor".into(), trust_types::Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
            obligation: None,
        }
    }

    fn dominance_strengthened_vc() -> VerificationCondition {
        let mut vc = dominance_vc();
        vc.formula = Formula::And(vec![dominance_p(), vc.formula]);
        vc
    }

    #[allow(clippy::too_many_arguments)]
    fn member<'a>(
        v: &'a VerificationCondition,
        original: &'a VerificationResult,
        s: &'a VerificationCondition,
        s_ev: &'a trust_ir::ProofEvidence,
        ext: Vec<String>,
        base: Vec<CallerDischargeProof<'a>>,
        scc: Vec<String>,
        ind: Vec<InductiveStepProof<'a>>,
    ) -> InductiveMemberProof<'a> {
        InductiveMemberProof {
            def_path: "helper".into(),
            original_vc: v,
            original_result: original,
            assumption: p_r1(),
            param_names: vec!["divisor".into()],
            param_types: vec![trust_types::Ty::i32()],
            gated_requires: vec![],
            strengthened: StrengthenedProof { vc: s, evidence: s_ev },
            enumerated_external_callers: ext,
            base_case_proofs: base,
            dominated_external_callers: vec![],
            enumerated_scc_callers: scc,
            inductive_step_proofs: ind,
        }
    }

    /// POSITIVE CONTROL — the `r1_recursive_self_stable_index` shape: a grounded
    /// self-loop whose base case and preservation step both carry certificates
    /// that REPLAY mints one sealed token per member.
    #[test]
    fn inductive_mint_mints_on_grounded_replayed_scc() {
        let (v, s) = (v_vc(), s_vc());
        let s_ev = evidence_for(&s);
        let c_vc = caller_vc("main");
        let c_ev = evidence_for(&c_vc);
        let i_vc = ind_vc();
        let i_ev = evidence_for(&i_vc);
        let certs = mint_inductive_caller_propagation_certificate(&[member(
            &v,
            &failed(),
            &s,
            &s_ev,
            vec!["main".into()],
            vec![caller_proof("main", &c_vc, &c_ev)],
            vec!["helper".into()],
            vec![ind_proof(&i_vc, &i_ev)],
        )])
        .expect("a grounded, fully replayed SCC must mint");
        assert_eq!(certs.len(), 1);
        let cert = &certs[0];
        assert_eq!(cert.provenance(), SealedCertificateProvenance::InductiveSccPropagation);
        assert_eq!(cert.discharge_identity(), &SealedVcIdentity::of(&v));
        assert_eq!(cert.strengthened_identity(), &SealedVcIdentity::of(&s));
        assert_eq!(cert.caller_site_count(), 2); // base site + preservation site
        assert_eq!(cert.covered_callers(), ["helper".to_string(), "main".to_string()]);
        assert!(cert.authorizes_operation(
            &v.kind.description(),
            &v.location.file,
            v.location.line_start,
            v.location.col_start
        ));
    }

    /// A dominance-suppressed base case is a real constraint and a real
    /// grounding entry.  The mint must re-run F5 against the exact member P it
    /// reconstructs, and must not require a nonexistent kernel row.
    #[test]
    fn inductive_mint_rederives_dominated_only_base_case() {
        let (v, s) = (dominance_vc(), dominance_strengthened_vc());
        let s_ev = evidence_for(&s);
        let caller = dominated_caller("main");
        let original = failed();
        let mut proof = scc_member(
            "helper",
            dominance_p(),
            &v,
            &original,
            &s,
            &s_ev,
            vec!["main".into()],
            vec![],
            vec![],
            vec![],
        );
        proof.param_names = vec!["divisor".into()];
        proof.param_types = vec![trust_types::Ty::i32()];
        proof.dominated_external_callers =
            vec![DominatedCallerClaim { caller: "main".into(), caller_function: &caller }];

        let certs = mint_inductive_caller_propagation_certificate(&[proof])
            .expect("exact-P dominance must ground the induction");
        assert_eq!(certs.len(), 1);
        assert_eq!(certs[0].caller_site_count(), 0);
        assert_eq!(certs[0].covered_callers(), ["main".to_string()]);
    }

    /// The exact coverage name and re-analysed function identity are one
    /// authority tuple.  A body for `other` cannot discharge the enumerated
    /// caller `main`, even when that body itself satisfies F5.
    #[test]
    fn inductive_mint_rejects_dominated_caller_body_swap() {
        let (v, s) = (dominance_vc(), dominance_strengthened_vc());
        let s_ev = evidence_for(&s);
        let wrong_body = dominated_caller("other");
        let original = failed();
        let mut proof = scc_member(
            "helper",
            dominance_p(),
            &v,
            &original,
            &s,
            &s_ev,
            vec!["main".into()],
            vec![],
            vec![],
            vec![],
        );
        proof.param_names = vec!["divisor".into()];
        proof.param_types = vec![trust_types::Ty::i32()];
        proof.dominated_external_callers =
            vec![DominatedCallerClaim { caller: "main".into(), caller_function: &wrong_body }];

        assert_eq!(
            mint_inductive_caller_propagation_certificate(&[proof]).map(|_| ()),
            Err(R1Reject::DominatedCallerIdentityMismatch {
                claimed: "main".into(),
                actual: "other".into(),
            })
        );
    }

    /// GROUNDING — an SCC with no external entry has no base case; the
    /// induction is ungrounded and must not mint, however good the
    /// preservation proofs are.
    #[test]
    fn inductive_mint_rejects_ungrounded_scc() {
        let (v, s) = (v_vc(), s_vc());
        let s_ev = evidence_for(&s);
        let i_vc = ind_vc();
        let i_ev = evidence_for(&i_vc);
        assert_eq!(
            mint_inductive_caller_propagation_certificate(&[member(
                &v,
                &failed(),
                &s,
                &s_ev,
                vec![],
                vec![],
                vec!["helper".into()],
                vec![ind_proof(&i_vc, &i_ev)],
            )])
            .map(|_| ()),
            Err(R1Reject::InductiveUngrounded)
        );
    }

    /// WITNESS-SWAP — a REAL certificate for the BASE-CASE obligation is not
    /// evidence for the preservation obligation. Identity-bound replay refuses.
    #[test]
    fn inductive_mint_rejects_swapped_preservation_evidence() {
        let (v, s) = (v_vc(), s_vc());
        let s_ev = evidence_for(&s);
        let c_vc = caller_vc("main");
        let c_ev = evidence_for(&c_vc);
        let i_vc = ind_vc();
        let mut bad = ind_proof(&i_vc, &c_ev); // genuine — but for the CALL SITE
        bad.evidence = &c_ev;
        assert_eq!(
            mint_inductive_caller_propagation_certificate(&[member(
                &v,
                &failed(),
                &s,
                &s_ev,
                vec!["main".into()],
                vec![caller_proof("main", &c_vc, &c_ev)],
                vec!["helper".into()],
                vec![bad],
            )])
            .map(|_| ()),
            Err(R1Reject::CallerNotReplayed {
                caller: "helper".into(),
                call_site: SourceSpan::default()
            })
        );
    }

    /// BASE-CASE HYGIENE — the base case must be UNCONDITIONAL: a member
    /// invariant smuggled into an external discharge's guard list would make
    /// the base case assume the induction it exists to ground.
    #[test]
    fn inductive_mint_rejects_hypothesis_in_base_case() {
        let (v, s) = (v_vc(), s_vc());
        let s_ev = evidence_for(&s);
        let c_vc = caller_vc("main");
        let c_ev = evidence_for(&c_vc);
        let i_vc = ind_vc();
        let i_ev = evidence_for(&i_vc);
        let mut conditional = caller_proof("main", &c_vc, &c_ev);
        conditional.allowed_guards = vec![p_r1()]; // the member's own P — unearned
        assert_eq!(
            mint_inductive_caller_propagation_certificate(&[member(
                &v,
                &failed(),
                &s,
                &s_ev,
                vec!["main".into()],
                vec![conditional],
                vec!["helper".into()],
                vec![ind_proof(&i_vc, &i_ev)],
            )])
            .map(|_| ()),
            Err(R1Reject::InductiveForeignHypothesis {
                member: "helper".into(),
                caller: "main".into()
            })
        );
    }

    /// COVERAGE — a recorded intra-SCC caller with no preservation discharge is
    /// an unproven recursive entry; refuse the whole SCC.
    #[test]
    fn inductive_mint_rejects_dropped_intra_scc_caller() {
        let (v, s) = (v_vc(), s_vc());
        let s_ev = evidence_for(&s);
        let c_vc = caller_vc("main");
        let c_ev = evidence_for(&c_vc);
        assert_eq!(
            mint_inductive_caller_propagation_certificate(&[member(
                &v,
                &failed(),
                &s,
                &s_ev,
                vec!["main".into()],
                vec![caller_proof("main", &c_vc, &c_ev)],
                vec!["helper".into()], // enumerated…
                vec![],                // …but never discharged
            )])
            .map(|_| ()),
            Err(R1Reject::CallerSetMismatch { expected: vec!["helper".into()], covered: vec![] })
        );
    }

    /// MEMBERSHIP — an enumerated "external" caller that IS an SCC member is an
    /// intra-SCC edge smuggled into the unconditional base case; refuse.
    #[test]
    fn inductive_mint_rejects_member_posing_as_external_caller() {
        let (v, s) = (v_vc(), s_vc());
        let s_ev = evidence_for(&s);
        let c_vc = caller_vc("helper");
        let c_ev = evidence_for(&c_vc);
        let i_vc = ind_vc();
        let i_ev = evidence_for(&i_vc);
        assert_eq!(
            mint_inductive_caller_propagation_certificate(&[member(
                &v,
                &failed(),
                &s,
                &s_ev,
                vec!["helper".into()],
                vec![caller_proof("helper", &c_vc, &c_ev)],
                vec!["helper".into()],
                vec![ind_proof(&i_vc, &i_ev)],
            )])
            .map(|_| ()),
            Err(R1Reject::InductiveCallerNotMember {
                member: "helper".into(),
                caller: "helper".into()
            })
        );
    }

    // ---- two-member SCC controls (mutual recursion `ping` ⇄ `pong`) ----
    //
    // Parameterized shapes: member `func` divides by its own parameter `dv`;
    // each recursive call forwards that parameter unchanged, so
    // `P_target[σ] = P_caller` over the caller's namespace.

    fn v_vc_named(func: &str, dv: &str) -> VerificationCondition {
        let divisor = || Formula::Var(dv.to_string(), trust_types::Sort::Int);
        let four = || Formula::Var("_4".to_string(), trust_types::Sort::Int);
        let five = || Formula::Var("_5".to_string(), trust_types::Sort::Bool);
        VerificationCondition {
            kind: trust_types::VcKind::DivisionByZero,
            function: func.into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![
                Formula::Eq(Box::new(four()), Box::new(divisor())),
                Formula::Eq(
                    Box::new(five()),
                    Box::new(Formula::Eq(Box::new(four()), Box::new(Formula::Int(0)))),
                ),
                five(),
            ]),
            contract_metadata: None,
            obligation: None,
        }
    }
    fn p_of(dv: &str) -> Formula {
        Formula::Not(Box::new(Formula::Eq(
            Box::new(Formula::Var(dv.to_string(), trust_types::Sort::Int)),
            Box::new(Formula::Int(0)),
        )))
    }
    fn s_vc_named(func: &str, dv: &str) -> VerificationCondition {
        let mut vc = v_vc_named(func, dv);
        let mut conj = conjuncts_of(&vc.formula);
        conj.insert(0, p_of(dv));
        vc.formula = Formula::And(conj);
        vc
    }
    /// The preservation obligation for the intra-SCC call `caller_fn → target_fn`
    /// forwarding `caller_dv` unchanged: `P_caller ∧ ¬P_target[σ]`, UNSAT.
    fn ind_vc_between(caller_fn: &str, target_fn: &str, caller_dv: &str) -> VerificationCondition {
        VerificationCondition {
            kind: trust_types::VcKind::Precondition { callee: target_fn.into() },
            function: caller_fn.into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![p_of(caller_dv), not(p_of(caller_dv))]),
            contract_metadata: None,
            obligation: None,
        }
    }
    fn ind_proof_between<'a>(
        caller_fn: &str,
        caller_dv: &str,
        vc: &'a VerificationCondition,
        evidence: &'a trust_ir::ProofEvidence,
    ) -> InductiveStepProof<'a> {
        InductiveStepProof {
            caller_member: caller_fn.into(),
            call_site: SourceSpan::default(),
            assumption_substituted: p_of(caller_dv), // P_target[σ] in the caller's namespace
            vc,
            allowed_guards: vec![p_of(caller_dv)], // the caller's OWN hypothesis
            evidence,
        }
    }
    fn caller_vc_for(caller: &str, callee: &str) -> VerificationCondition {
        VerificationCondition {
            kind: trust_types::VcKind::Precondition { callee: callee.into() },
            function: caller.into(),
            location: SourceSpan::default(),
            formula: not(p_sigma()),
            contract_metadata: None,
            obligation: None,
        }
    }
    #[allow(clippy::too_many_arguments)]
    fn scc_member<'a>(
        def_path: &str,
        p: Formula,
        v: &'a VerificationCondition,
        original: &'a VerificationResult,
        s: &'a VerificationCondition,
        s_ev: &'a trust_ir::ProofEvidence,
        ext: Vec<String>,
        base: Vec<CallerDischargeProof<'a>>,
        scc: Vec<String>,
        ind: Vec<InductiveStepProof<'a>>,
    ) -> InductiveMemberProof<'a> {
        InductiveMemberProof {
            def_path: def_path.into(),
            original_vc: v,
            original_result: original,
            assumption: p,
            param_names: vec!["divisor".into()],
            param_types: vec![trust_types::Ty::i32()],
            gated_requires: vec![],
            strengthened: StrengthenedProof { vc: s, evidence: s_ev },
            enumerated_external_callers: ext,
            base_case_proofs: base,
            dominated_external_callers: vec![],
            enumerated_scc_callers: scc,
            inductive_step_proofs: ind,
        }
    }

    /// POSITIVE — a genuine 2-member mutual SCC with DISTINCT invariants
    /// (`ping` over `divisor`, `pong` over `k`), grounded at `main → ping`.
    #[test]
    fn inductive_mint_mints_two_member_scc_with_distinct_invariants() {
        let (vp, sp) = (v_vc_named("ping", "divisor"), s_vc_named("ping", "divisor"));
        let (vq, sq) = (v_vc_named("pong", "k"), s_vc_named("pong", "k"));
        let sp_ev = evidence_for(&sp);
        let sq_ev = evidence_for(&sq);
        let c_vc = caller_vc_for("main", "ping");
        let c_ev = evidence_for(&c_vc);
        let i_pq = ind_vc_between("ping", "pong", "divisor"); // targets pong
        let i_pq_ev = evidence_for(&i_pq);
        let i_qp = ind_vc_between("pong", "ping", "k"); // targets ping
        let i_qp_ev = evidence_for(&i_qp);
        let f = failed();
        let certs = mint_inductive_caller_propagation_certificate(&[
            scc_member(
                "ping",
                p_of("divisor"),
                &vp,
                &f,
                &sp,
                &sp_ev,
                vec!["main".into()],
                vec![caller_proof("main", &c_vc, &c_ev)],
                vec!["pong".into()],
                vec![ind_proof_between("pong", "k", &i_qp, &i_qp_ev)],
            ),
            scc_member(
                "pong",
                p_of("k"),
                &vq,
                &f,
                &sq,
                &sq_ev,
                vec![],
                vec![],
                vec!["ping".into()],
                vec![ind_proof_between("ping", "divisor", &i_pq, &i_pq_ev)],
            ),
        ])
        .expect("a grounded 2-member SCC with distinct invariants must mint");
        assert_eq!(certs.len(), 2);
        assert_eq!(certs[0].provenance(), SealedCertificateProvenance::InductiveSccPropagation);
        assert_eq!(certs[0].covered_callers(), ["main".to_string(), "pong".to_string()]);
        assert_eq!(certs[1].covered_callers(), ["ping".to_string()]);
    }

    /// POSITIVE + the hypothesis-hygiene REGRESSION test: a SYMMETRIC 2-member
    /// SCC infers textually IDENTICAL invariants for both members (both divide
    /// by a parameter named `divisor`). The spliced own-hypothesis then equals
    /// the other member's invariant BY VALUE — a per-provenance hygiene check
    /// would misread it as foreign and refuse the whole SCC. Value-based
    /// hygiene must mint.
    #[test]
    fn inductive_mint_mints_symmetric_scc_with_identical_invariants() {
        let (vp, sp) = (v_vc_named("ping", "divisor"), s_vc_named("ping", "divisor"));
        let (vq, sq) = (v_vc_named("pong", "divisor"), s_vc_named("pong", "divisor"));
        let sp_ev = evidence_for(&sp);
        let sq_ev = evidence_for(&sq);
        let c_vc = caller_vc_for("main", "ping");
        let c_ev = evidence_for(&c_vc);
        let i_pq = ind_vc_between("ping", "pong", "divisor");
        let i_pq_ev = evidence_for(&i_pq);
        let i_qp = ind_vc_between("pong", "ping", "divisor");
        let i_qp_ev = evidence_for(&i_qp);
        let f = failed();
        let certs = mint_inductive_caller_propagation_certificate(&[
            scc_member(
                "ping",
                p_of("divisor"),
                &vp,
                &f,
                &sp,
                &sp_ev,
                vec!["main".into()],
                vec![caller_proof("main", &c_vc, &c_ev)],
                vec!["pong".into()],
                vec![ind_proof_between("pong", "divisor", &i_qp, &i_qp_ev)],
            ),
            scc_member(
                "pong",
                p_of("divisor"),
                &vq,
                &f,
                &sq,
                &sq_ev,
                vec![],
                vec![],
                vec!["ping".into()],
                vec![ind_proof_between("ping", "divisor", &i_pq, &i_pq_ev)],
            ),
        ])
        .expect("identical invariants are the caller's OWN hypothesis by value — must mint");
        assert_eq!(certs.len(), 2);
    }

    /// A guard in the INDUCTIVE-STEP position equal to a DIFFERENT member's
    /// invariant is an unearned hypothesis — the arm the value-based hygiene
    /// fix must keep rejecting.
    #[test]
    fn inductive_mint_rejects_foreign_hypothesis_in_inductive_step() {
        let (vp, sp) = (v_vc_named("ping", "divisor"), s_vc_named("ping", "divisor"));
        let (vq, sq) = (v_vc_named("pong", "k"), s_vc_named("pong", "k"));
        let sp_ev = evidence_for(&sp);
        let sq_ev = evidence_for(&sq);
        let c_vc = caller_vc_for("main", "ping");
        let c_ev = evidence_for(&c_vc);
        let i_pq = ind_vc_between("ping", "pong", "divisor");
        let i_pq_ev = evidence_for(&i_pq);
        let i_qp = ind_vc_between("pong", "ping", "k");
        let i_qp_ev = evidence_for(&i_qp);
        let f = failed();
        // Corrupt the ping→pong step: smuggle pong's OWN invariant (`k != 0`,
        // foreign to caller ping) into its guard list.
        let mut poisoned = ind_proof_between("ping", "divisor", &i_pq, &i_pq_ev);
        poisoned.allowed_guards.push(p_of("k"));
        assert_eq!(
            mint_inductive_caller_propagation_certificate(&[
                scc_member(
                    "ping",
                    p_of("divisor"),
                    &vp,
                    &f,
                    &sp,
                    &sp_ev,
                    vec!["main".into()],
                    vec![caller_proof("main", &c_vc, &c_ev)],
                    vec!["pong".into()],
                    vec![ind_proof_between("pong", "k", &i_qp, &i_qp_ev)],
                ),
                scc_member(
                    "pong",
                    p_of("k"),
                    &vq,
                    &f,
                    &sq,
                    &sq_ev,
                    vec![],
                    vec![],
                    vec!["ping".into()],
                    vec![poisoned],
                ),
            ])
            .map(|_| ()),
            Err(R1Reject::InductiveForeignHypothesis {
                member: "pong".into(),
                caller: "ping".into()
            })
        );
    }

    /// Two member bundles claiming one def_path ⇒ ambiguous invariant table.
    #[test]
    fn inductive_mint_rejects_duplicate_member() {
        let (v, s) = (v_vc(), s_vc());
        let s_ev = evidence_for(&s);
        let c_vc = caller_vc("main");
        let c_ev = evidence_for(&c_vc);
        let i_vc = ind_vc();
        let i_ev = evidence_for(&i_vc);
        let f = failed();
        let bundle = || {
            member(
                &v,
                &f,
                &s,
                &s_ev,
                vec!["main".into()],
                vec![caller_proof("main", &c_vc, &c_ev)],
                vec!["helper".into()],
                vec![ind_proof(&i_vc, &i_ev)],
            )
        };
        assert_eq!(
            mint_inductive_caller_propagation_certificate(&[bundle(), bundle()]).map(|_| ()),
            Err(R1Reject::InductiveMemberDuplicate { member: "helper".into() })
        );
    }

    /// A member with neither an external caller nor an intra-SCC call into it:
    /// its `P` is established nowhere — refuse rather than mint vacuously.
    #[test]
    fn inductive_mint_rejects_unconstrained_member() {
        let (v, s) = (v_vc(), s_vc());
        let s_ev = evidence_for(&s);
        assert_eq!(
            mint_inductive_caller_propagation_certificate(&[member(
                &v,
                &failed(),
                &s,
                &s_ev,
                vec![],
                vec![],
                vec![],
                vec![],
            )])
            .map(|_| ()),
            Err(R1Reject::InductiveMemberUnconstrained { member: "helper".into() })
        );
    }

    /// PROVENANCE — per-mono aggregation is defined over DIRECT tokens only.
    /// A direct token aggregates (and the result is marked as an aggregation);
    /// an inductive token must refuse, or its conditional intra-SCC discharges
    /// would be laundered into an unconditional-looking union.
    #[test]
    fn generic_aggregation_requires_direct_tokens() {
        let (v, s) = (v_vc(), s_vc());
        let s_ev = evidence_for(&s);
        let c_vc = caller_vc("main");
        let c_ev = evidence_for(&c_vc);
        let direct = mint_caller_propagation_certificate(
            &v,
            &failed(),
            &p_r1(),
            &[],
            &StrengthenedProof { vc: &s, evidence: &s_ev },
            &CallerCoverage::Total,
            &["main".to_string()],
            &[caller_proof("main", &c_vc, &c_ev)],
        )
        .expect("direct token mints");
        let agg = seal_generic_flip(vec![direct]).expect("direct tokens aggregate");
        assert_eq!(agg.provenance(), SealedCertificateProvenance::GenericMonoAggregation);

        let i_vc = ind_vc();
        let i_ev = evidence_for(&i_vc);
        let inductive = mint_inductive_caller_propagation_certificate(&[member(
            &v,
            &failed(),
            &s,
            &s_ev,
            vec!["main".into()],
            vec![caller_proof("main", &c_vc, &c_ev)],
            vec!["helper".into()],
            vec![ind_proof(&i_vc, &i_ev)],
        )])
        .expect("inductive token mints")
        .remove(0);
        assert_eq!(
            seal_generic_flip(vec![inductive]).map(|_| ()),
            Err(R1Reject::GenericAggregationOfNonDirectToken)
        );
    }
}
