// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `CleanCic` evidence for an E9 `ensures` discharge (cited theorem re-check
//! and uncited island definitional equality).
//!
//! WHY THIS EXISTS. The compiler's E9 lanes kernel-discharge an `ensures`
//! clause and seal an `EnsuresCitationDischarge` authority to the row, but
//! until now they kept only a VERDICT — the goal and the proof term the kernel
//! judged were dropped on the floor. The authenticated publication boundary
//! (`targo-trust`, `clean_cic_transport_proof_is_publishable`) publishes a
//! favorable row only when it carries a content-addressed `CleanCic` payload,
//! so every contract discharged by a Lean definition or theorem was WITHHELD
//! (`Gate: INCONCLUSIVE`) although the kernel had certified it. The fix is to
//! PRODUCE the missing certificate, never to relax the check that caught it.
//!
//! WHAT THE PAYLOAD IS. The same `ProofEvidence::CleanCic { term, context,
//! lineage, kernel_recheck: None }` carrier every other closed kernel lane in
//! this crate emits, with a lane-specific `context` schema (trust-ir: "the
//! exact `term`/`context` wire schema is anchor-specific"):
//!
//! * `term` — `serialize_term` of the CLOSED proof term the kernel judged: the
//!   cited theorem's own value, or the constructed `fun … => Eq.refl lhs`, and
//!   for a multi-clause surface the `And.intro` chain over the per-clause
//!   proofs (the compiler's conjunction rule discharges the rows only when
//!   EVERY clause certifies, so the conjunction is what the rows rest on);
//! * `context` — a canonical, self-identifying binding record
//!   ([`CONTEXT_MAGIC`]): the function's self spelling, the typed parameters,
//!   every clause's authored text with its route and referent (theorem name or
//!   island definition), the `serialize_term` bytes of the exact elaborated
//!   goal, and a SHA-256 ([`environment_closure_digest`]) over each clause
//!   referent's declaration followed by the complete kernel-environment closure
//!   the judgment reaches — every constant's name, universe parameters, kind,
//!   type and value. BE PRECISE ABOUT WHAT THAT PINS. The island definitions and
//!   the function's E6-imported defining equation are pinned because the audited
//!   judgment reaches them. A CITED THEOREM IS NOT REACHED: its proof value is
//!   inlined into `term`, so the theorem constant is normally absent from the
//!   audit's own closure — what pins the theorem's proof is the `term` bytes
//!   themselves, and the referent section of the digest pins the DECLARATION the
//!   recorded name resolves to. Requiring the recorded NAME to be the one whose
//!   value `term` carries is [`recheck_ensures_discharge`]'s regeneration step,
//!   which rebuilds the proof from that referent and demands byte equality;
//!   [`audit_presented_ensures_discharge`] alone does not;
//! * `lineage` — SHA-256 over term, context and the row's full canonical
//!   obligation identity (the same `ObligationIdentity::from_vc` bytes the
//!   violation-refutation lane binds), under a DISTINCT domain so an E9
//!   certificate can never be confused with a violation refutation.
//!
//! WHAT MINTS IT. [`certify_ensures_discharge`] re-elaborates every clause
//! through the same `elaborate_ensures_in` entry the grade call used, WITH THE
//! SAME [`trust_spec_elab::ProofClauseInputs`], rebuilds the proof, and runs the
//! FULL `Environment::audit_certification` on the (composite) judgment. Nothing
//! is minted unless that audit is clean. This is deliberately at least as strict
//! as either grade route — the uncited defeq route grades with `check_type`
//! alone — so a payload can be absent for a row the compiler discharged, never
//! present for one it would not have.
//!
//! Trust (nat-lift, 2026-09-17): the clause inputs are a PARAMETER of this lane
//! because it is the FIFTH user-clause elaboration site. Before this it called
//! the unmoded `elaborate_ensures`, i.e. `ClauseMode::Strict`, so a clause
//! carrying `e as nat` / `e as int` returned `unsupported term shape` here and
//! the whole function minted NOTHING — silently, and not only for the lifted
//! clause: `certify_ensures_discharge` judges the function's complete surface,
//! so one lifted clause would have withheld its unlifted siblings' publishable
//! evidence too. Measured by `a_lifted_clause_still_mints_its_certificate`.
//!
//! BOUND, disclosed rather than hidden: a clause whose lift needs the SEEDED
//! signed value model (`as int` on an `iN` term) mints no certificate. The
//! producer would have to judge in a seeded CLONE of the environment, while
//! [`audit_presented_ensures_discharge`] — which holds only the environment and
//! the bytes — would re-derive `environment_closure_digest` over the UNSEEDED
//! one and refuse its own producer's payload. Rather than mint a payload no
//! consumer can audit, `rebuild_judgment` returns `None` and the rows ship
//! evidence-free, exactly as every other miss does. Measured by
//! `a_signed_lifted_clause_mints_no_certificate_and_that_is_the_disclosed_bound`.
//!
//! WHAT RE-CHECKS IT. [`recheck_ensures_discharge`] is the consumer half: it
//! regenerates the canonical payload from the consumer's OWN inputs, requires
//! byte equality, independently decodes and kernel-audits the PRESENTED bytes,
//! and re-binds the lineage to the consumer's row. A holder of only the
//! environment can still run [`audit_presented_ensures_discharge`].

use clean_auto::bridge::ay_contract::{deserialize_term, serialize_term};
use clean_kernel::{ConstantKind, Environment, Expr, Name};
use sha2::{Digest, Sha256};
use trust_types::VerificationCondition;

mod typed;
pub use typed::{certify_ensures_discharge_with_domains, recheck_ensures_discharge_with_domains};

#[cfg(test)]
mod typed_tests;

/// Self-identifying prefix of the `context` binding record. A `ReducedContext`
/// (the violation-refutation lanes' `context`) can never begin with it, and a
/// decoder that does not see it refuses the payload.
const CONTEXT_MAGIC: &[u8] = b"trust-certify.e9-ensures-discharge.context.v1\0";

/// Lineage domain. Distinct from `trust-certify.cleancic.v3` (violation
/// refutations): the two certificate families prove different KINDS of claim
/// and must never validate under each other's binding.
const LINEAGE_DOMAIN: &[u8] = b"trust-certify.cleancic.e9-ensures-discharge.v1";

/// Domain of the kernel-environment closure digest.
const ENVIRONMENT_DOMAIN: &[u8] = b"trust-certify.e9-ensures-discharge.environment.v1";

/// The transport ships `term` as a JSON byte array on EVERY row the discharge
/// covers, so an unbounded cited proof would multiply into the report. A proof
/// term above this bound mints no payload (the row is then withheld at
/// publication exactly as it was before this lane existed — fail closed).
const MAX_TERM_BYTES: usize = 1024 * 1024;

/// Bounds for the untrusted-context decoder.
const MAX_CONTEXT_FIELD_BYTES: usize = 8 * 1024 * 1024;
const MAX_CONTEXT_ENTRIES: u64 = 4096;

const ROUTE_TAG_CITED_THEOREM: u8 = 1;
const ROUTE_TAG_ISLAND_DEFEQ: u8 = 2;

/// How one `ensures` clause was discharged.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EnsuresDischargeRoute<'a> {
    /// `ensures Q by <theorem>` — the cited theorem's proof term is the proof.
    CitedTheorem(&'a str),
    /// Uncited clause naming an island definition — `fun … => Eq.refl lhs`.
    IslandDefeq(&'a str),
}

/// One clause of the function's complete `ensures` surface, with THE SAME
/// inputs its grade call received (post-prime-rewrite text, the same facet
/// table).
#[derive(Clone, Copy)]
pub struct EnsuresDischargeClause<'a> {
    pub clause_src: &'a str,
    pub route: EnsuresDischargeRoute<'a>,
    pub facets: &'a trust_spec_elab::FacetTable,
}

/// The row-independent half of the evidence: the kernel-audited judgment for
/// one function's complete `ensures` surface. Bind it to each discharged row
/// with [`Self::evidence_for_row`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnsuresDischargeCertificate {
    term: Vec<u8>,
    context: Vec<u8>,
    /// KR0 switch: the Clean reference entry's certificate for the closed
    /// judgment `proof : goal`, checked in an entry built from the island
    /// environment, or `None` when the entry refused it. The compiler mints
    /// the `Certified` E9 authority only with `Some`.
    reference: Option<crate::reference_mint::ReferenceCertificate>,
}

impl EnsuresDischargeCertificate {
    /// Bind this certificate to one exact obligation row. `None` when the row
    /// exceeds the identity depth gate (the same fail-closed bound
    /// `certify_vc` applies before serializing an obligation).
    #[must_use]
    pub fn evidence_for_row(&self, vc: &VerificationCondition) -> Option<trust_ir::ProofEvidence> {
        let lineage = row_lineage(&self.term, &self.context, vc)?;
        let evidence = trust_ir::ProofEvidence::CleanCic {
            term: self.term.clone(),
            context: self.context.clone(),
            lineage,
            kernel_recheck: None,
        };
        // KR0 switch: the row's payload carries the surface's reference
        // certificate (`crate::reference_certificate_for`).
        crate::reference_mint::register_evidence(&evidence, self.reference.as_ref());
        Some(evidence)
    }

    /// The reference entry's certificate for this surface's judgment, if the
    /// entry accepted it.
    #[must_use]
    pub fn reference(&self) -> Option<&crate::reference_mint::ReferenceCertificate> {
        self.reference.as_ref()
    }
}

/// The judgment the kernel audited, before serialization.
struct Judgment {
    goal: Expr,
    proof: Expr,
    environment_digest: [u8; 32],
    dependency_count: u64,
}

/// Decoded `context` binding record.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ContextRecord {
    self_fn_name: String,
    params: Vec<(String, String)>,
    /// `(route tag, referent, clause text)` in authored order.
    clauses: Vec<(u8, String, String)>,
    goal: Vec<u8>,
    environment_digest: [u8; 32],
    dependency_count: u64,
}

/// Mint the kernel-audited certificate for a function whose COMPLETE `ensures`
/// surface the E9 lane discharged. `clauses` must be every clause, in authored
/// order, each with the inputs its grade call used. Fail-closed (`None`) on any
/// elaboration, lookup, audit, serialization or size miss — the caller's
/// verdict is unaffected; the row simply carries no publishable payload.
#[must_use]
pub fn certify_ensures_discharge(
    env: &Environment,
    clauses: &[EnsuresDischargeClause<'_>],
    param_types: &[(&str, &str)],
    self_fn_name: &str,
    inputs: &trust_spec_elab::ProofClauseInputs,
) -> Option<EnsuresDischargeCertificate> {
    let judgment = rebuild_judgment(env, clauses, param_types, self_fn_name, inputs)?;
    let term = serialize_term(&judgment.proof).ok()?;
    // T3 L4 (C06a): the term withhold is a CAP site (`trust_types::audit_ledger`).
    if term.is_empty()
        || trust_types::audit_ledger::cap_hit_if(
            term.len() > MAX_TERM_BYTES,
            "crates/trust-certify/src/clean_island/ensures_evidence.rs:MAX_TERM_BYTES",
        )
    {
        return None;
    }
    let goal = serialize_term(&judgment.goal).ok()?;
    let record = ContextRecord {
        self_fn_name: self_fn_name.to_string(),
        params: param_types.iter().map(|(n, t)| ((*n).to_string(), (*t).to_string())).collect(),
        clauses: clauses
            .iter()
            .map(|clause| {
                let (tag, referent) = route_fields(clause.route);
                (tag, referent.to_string(), clause.clause_src.to_string())
            })
            .collect(),
        goal,
        environment_digest: judgment.environment_digest,
        dependency_count: judgment.dependency_count,
    };
    let context = encode_context(&record);
    // Defense in depth, as every closed lane in this crate does: the
    // SERIALIZED payload must decode back to exactly the judgment the kernel
    // audited, or nothing is minted.
    if decode_context(&context).as_ref() != Some(&record)
        || deserialize_term(&term).ok().as_ref() != Some(&judgment.proof)
        || deserialize_term(&record.goal).ok().as_ref() != Some(&judgment.goal)
    {
        return None;
    }
    // KR0 switch: the same closed judgment, through the reference entry.
    let reference =
        crate::reference_mint::check_closed_in(env, &judgment.goal, &judgment.proof).ok();
    Some(EnsuresDischargeCertificate { term, context, reference })
}

/// Consumer-side re-check of an E9 `CleanCic` payload against the consumer's
/// OWN environment, clause inputs and obligation row. `true` only when
///
/// * the canonical payload regenerated from those inputs (full kernel audit
///   included) is byte-identical to the presented `term` and `context`;
/// * the PRESENTED bytes independently decode and kernel-audit
///   ([`audit_presented_ensures_discharge`]); and
/// * the lineage re-binds to `vc`'s complete canonical identity.
///
/// So a tampered term fails the byte comparison and the kernel audit, a payload
/// minted for a different clause/theorem/function/environment fails the
/// regeneration, and a payload transplanted onto another row fails the lineage.
#[must_use]
pub fn recheck_ensures_discharge(
    env: &Environment,
    clauses: &[EnsuresDischargeClause<'_>],
    param_types: &[(&str, &str)],
    self_fn_name: &str,
    inputs: &trust_spec_elab::ProofClauseInputs,
    vc: &VerificationCondition,
    evidence: &trust_ir::ProofEvidence,
) -> bool {
    let trust_ir::ProofEvidence::CleanCic { term, context, lineage, kernel_recheck: None } =
        evidence
    else {
        return false;
    };
    let Some(canonical) =
        certify_ensures_discharge(env, clauses, param_types, self_fn_name, inputs)
    else {
        return false;
    };
    canonical.term == *term
        && canonical.context == *context
        && audit_presented_ensures_discharge(env, term, context)
        && row_lineage(term, context, vc).as_ref() == Some(lineage)
}

/// Kernel-audit the PRESENTED payload with nothing but the environment: decode
/// the binding record, deserialize the goal and the proof term it carries, run
/// the full certification audit on `term : goal`, and require the recorded
/// kernel-environment closure digest to match the environment at hand.
///
/// This establishes "these bytes are a clean kernel proof of the proposition
/// they name, in an environment whose recorded referents and whose whole
/// reachable closure are the producer's". It does NOT establish that the
/// proposition is the compiler's elaboration of any clause, nor that the
/// recorded referent is the constant whose value `term` carries — both are
/// [`recheck_ensures_discharge`]'s regeneration step.
#[must_use]
pub fn audit_presented_ensures_discharge(
    env: &Environment,
    term_bytes: &[u8],
    context_bytes: &[u8],
) -> bool {
    if context_bytes.starts_with(typed::CONTEXT_MAGIC) {
        return typed::audit_presented(env, term_bytes, context_bytes);
    }
    if term_bytes.is_empty()
        || trust_types::audit_ledger::cap_hit_if(
            term_bytes.len() > MAX_TERM_BYTES,
            "crates/trust-certify/src/clean_island/ensures_evidence.rs:MAX_TERM_BYTES",
        )
    {
        return false;
    }
    let Some(record) = decode_context(context_bytes) else {
        return false;
    };
    let (Ok(goal), Ok(term)) = (deserialize_term(&record.goal), deserialize_term(term_bytes))
    else {
        return false;
    };
    let audit = env.audit_certification(&goal, &term);
    if !audit.is_certified() {
        return false;
    }
    let referents: Vec<&str> =
        record.clauses.iter().map(|(_, referent, _)| referent.as_str()).collect();
    u64::try_from(audit.dependencies.len()).ok() == Some(record.dependency_count)
        && environment_closure_digest(env, &referents, &audit.dependencies)
            == Some(record.environment_digest)
}

fn route_fields(route: EnsuresDischargeRoute<'_>) -> (u8, &str) {
    match route {
        EnsuresDischargeRoute::CitedTheorem(theorem) => (ROUTE_TAG_CITED_THEOREM, theorem),
        EnsuresDischargeRoute::IslandDefeq(definition) => (ROUTE_TAG_ISLAND_DEFEQ, definition),
    }
}

/// Re-derive the judgment from the clause inputs and kernel-audit it.
fn rebuild_judgment(
    env: &Environment,
    clauses: &[EnsuresDischargeClause<'_>],
    param_types: &[(&str, &str)],
    self_fn_name: &str,
    inputs: &trust_spec_elab::ProofClauseInputs,
) -> Option<Judgment> {
    if clauses.is_empty() || self_fn_name.is_empty() {
        return None;
    }
    rebuild_judgment_from(
        env,
        clauses,
        |clause| {
            // Trust (nat-lift): the SAME entry, mode and inputs the grade call ran
            // with. See this module's header: at `Strict` this site silently
            // withheld the whole function's evidence for any surface carrying a
            // lift.
            let elaborated = trust_spec_elab::elaborate_ensures_in(
                clause.clause_src,
                param_types,
                self_fn_name,
                clause.facets,
                inputs,
            )
            .ok()?;
            // Trust (nat-lift, disclosed bound): a SEEDED signed lift would have to
            // be judged in a clone of `env`, and `audit_presented_ensures_discharge`
            // re-derives the closure digest over the environment it is handed — so
            // the producer's own payload would fail the consumer's presented audit.
            // Mint nothing rather than an unauditable payload.
            if !elaborated.required_signed_lift_widths.is_empty() {
                return None;
            }
            Some(elaborated.goal)
        },
        environment_closure_digest,
    )
}

/// Shared production authority path for scalar v1 and exact-domain v2.
/// Only goal construction and the versioned environment encoding vary.
fn rebuild_judgment_from(
    env: &Environment,
    clauses: &[EnsuresDischargeClause<'_>],
    mut elaborate: impl FnMut(&EnsuresDischargeClause<'_>) -> Option<Expr>,
    digest: fn(&Environment, &[&str], &[Name]) -> Option<[u8; 32]>,
) -> Option<Judgment> {
    let mut composite: Option<(Expr, Expr)> = None;
    for clause in clauses {
        let goal = elaborate(clause)?;
        // The same ill-typed-goal gate both grade routes apply first.
        if super::reject_untyped_goal(env, &goal).is_some() {
            return None;
        }
        let proof = match clause.route {
            EnsuresDischargeRoute::CitedTheorem(theorem) => cited_theorem_proof(env, theorem)?,
            EnsuresDischargeRoute::IslandDefeq(definition) => {
                // The referent is recorded in the payload, so it must at least
                // BE what the record says: an unfoldable environment definition.
                let info = env.get_const(&Name::from_string(definition))?;
                if info.kind != ConstantKind::Definition || info.value.is_none() {
                    return None;
                }
                super::defeq_closed_proof(&goal).ok()?
            }
        };
        composite = Some(match composite {
            None => (goal, proof),
            Some((goal_so_far, proof_so_far)) => (
                and_prop(goal_so_far.clone(), goal.clone()),
                and_intro(goal_so_far, goal, proof_so_far, proof),
            ),
        });
    }
    let (goal, proof) = composite?;
    // THE authority step: root judgment + complete reachable closure, the same
    // audit `cert_meter::grade` delegates to. Anything short of clean mints
    // nothing — including a defeq judgment whose grade used `check_type` only.
    let audit = env.audit_certification(&goal, &proof);
    if !audit.is_certified() {
        return None;
    }
    let referents: Vec<&str> = clauses.iter().map(|clause| route_fields(clause.route).1).collect();
    let environment_digest = digest(env, &referents, &audit.dependencies)?;
    let dependency_count = u64::try_from(audit.dependencies.len()).ok()?;
    Some(Judgment { goal, proof, environment_digest, dependency_count })
}

/// The cited theorem's proof term, behind the same declaration gates
/// `grade_cited_theorem_against_goal` applies before grading.
fn cited_theorem_proof(env: &Environment, theorem: &str) -> Option<Expr> {
    let name = Name::from_string(theorem);
    let info = env.get_const(&name)?;
    if info.kind != ConstantKind::Theorem || env.is_unsafe(&name) || env.is_partial(&name) {
        return None;
    }
    info.value.clone()
}

fn and_prop(a: Expr, b: Expr) -> Expr {
    Expr::app(Expr::app(Expr::const_(Name::from_string("And"), Vec::new()), a), b)
}

/// `And.intro a b proof_a proof_b` — the spelling `defeq_proof_for_goal`
/// already hands the kernel for a conjunctive clause.
fn and_intro(a: Expr, b: Expr, proof_a: Expr, proof_b: Expr) -> Expr {
    let intro = Expr::const_(Name::from_string("And.intro"), Vec::new());
    Expr::app(Expr::app(Expr::app(Expr::app(intro, a), b), proof_a), proof_b)
}

fn update_field(hasher: &mut Sha256, field: &[u8]) {
    hasher.update((field.len() as u64).to_le_bytes());
    hasher.update(field);
}

/// One constant's COMPLETE declaration: name, universe parameters, kind, type,
/// value. `None` when the name is not in this environment or does not
/// serialize.
fn update_declaration(hasher: &mut Sha256, env: &Environment, name: &Name) -> Option<()> {
    let info = env.get_const(name)?;
    update_field(hasher, name.to_string().as_bytes());
    hasher.update((info.level_params.len() as u64).to_le_bytes());
    for level_param in &info.level_params {
        update_field(hasher, level_param.to_string().as_bytes());
    }
    hasher.update([match info.kind {
        ConstantKind::Definition => 1u8,
        ConstantKind::Theorem => 2,
        ConstantKind::Opaque => 3,
        ConstantKind::Axiom => 4,
    }]);
    update_field(hasher, &serialize_term(&info.type_).ok()?);
    match info.value.as_ref() {
        None => hasher.update([0u8]),
        Some(value) => {
            hasher.update([1u8]);
            update_field(hasher, &serialize_term(value).ok()?);
        }
    }
    Some(())
}

/// SHA-256 over two declaration sets, each as [`update_declaration`] spells one:
///
/// * `referents` — the constant each clause's recorded route NAMES, in clause
///   order. Hashing these is what keeps the recorded referent from being a free
///   label: the name must resolve in the environment at hand and its whole
///   declaration must be the one the producer saw. It does NOT by itself bind
///   the referent to the proof component that travels in `term` — the cited
///   theorem's proof VALUE is inlined into `term`, so the theorem CONSTANT is
///   normally not in the audit's own closure at all. That binding is
///   [`recheck_ensures_discharge`]'s regeneration step, which rebuilds the proof
///   FROM the recorded referent and demands byte equality.
/// * `dependencies` — the complete constant closure the audited judgment
///   reaches, in the audit's own sorted order (the island definitions and the
///   function's E6-imported defining equation are pinned here).
///
/// `None` if any declaration is missing or does not serialize.
fn environment_closure_digest(
    env: &Environment,
    referents: &[&str],
    dependencies: &[Name],
) -> Option<[u8; 32]> {
    let mut hasher = Sha256::new();
    update_field(&mut hasher, ENVIRONMENT_DOMAIN);
    hasher.update((referents.len() as u64).to_le_bytes());
    for referent in referents {
        update_declaration(&mut hasher, env, &Name::from_string(referent))?;
    }
    hasher.update((dependencies.len() as u64).to_le_bytes());
    for name in dependencies {
        update_declaration(&mut hasher, env, name)?;
    }
    let mut digest = [0u8; 32];
    digest.copy_from_slice(&hasher.finalize());
    Some(digest)
}

/// Lineage of one row: term, context, and the row's complete canonical
/// obligation identity, each length-prefixed (injective), under this lane's
/// own domain. Identity construction follows `certify_vc`'s discipline —
/// iterative depth gate on the caller's thread, serde recursion on the
/// large-stack thread.
fn row_lineage(
    term: &[u8],
    context: &[u8],
    vc: &VerificationCondition,
) -> Option<trust_ir::ProofDigest> {
    let max_depth = crate::vc_max_depth_within_gate(vc)?;
    let compute = || {
        let identity = crate::ObligationIdentity::from_vc(vc)?;
        let mut hasher = Sha256::new();
        update_field(&mut hasher, LINEAGE_DOMAIN);
        for field in [term, context, identity.encoded.as_slice()] {
            update_field(&mut hasher, field);
        }
        let mut bytes = [0u8; 32];
        bytes.copy_from_slice(&hasher.finalize());
        Some(trust_ir::ProofDigest::sha256(bytes))
    };
    if max_depth <= crate::SHALLOW_CALLER_STACK_MAX_DEPTH {
        return compute();
    }
    crate::on_certify_stack_if_needed(compute)
}

fn push_field(out: &mut Vec<u8>, field: &[u8]) {
    out.extend_from_slice(&(field.len() as u64).to_le_bytes());
    out.extend_from_slice(field);
}

fn encode_context(record: &ContextRecord) -> Vec<u8> {
    let mut out = CONTEXT_MAGIC.to_vec();
    push_field(&mut out, record.self_fn_name.as_bytes());
    out.extend_from_slice(&(record.params.len() as u64).to_le_bytes());
    for (name, ty) in &record.params {
        push_field(&mut out, name.as_bytes());
        push_field(&mut out, ty.as_bytes());
    }
    out.extend_from_slice(&(record.clauses.len() as u64).to_le_bytes());
    for (tag, referent, clause) in &record.clauses {
        out.push(*tag);
        push_field(&mut out, referent.as_bytes());
        push_field(&mut out, clause.as_bytes());
    }
    push_field(&mut out, &record.goal);
    out.extend_from_slice(&record.environment_digest);
    out.extend_from_slice(&record.dependency_count.to_le_bytes());
    out
}

/// Bounded cursor over untrusted context bytes.
struct Reader<'a> {
    bytes: &'a [u8],
}

impl<'a> Reader<'a> {
    fn take(&mut self, len: usize) -> Option<&'a [u8]> {
        if len > self.bytes.len() {
            return None;
        }
        let (head, tail) = self.bytes.split_at(len);
        self.bytes = tail;
        Some(head)
    }

    fn u64(&mut self) -> Option<u64> {
        let mut raw = [0u8; 8];
        raw.copy_from_slice(self.take(8)?);
        Some(u64::from_le_bytes(raw))
    }

    fn count(&mut self) -> Option<u64> {
        self.u64().filter(|count| *count <= MAX_CONTEXT_ENTRIES)
    }

    fn field(&mut self) -> Option<&'a [u8]> {
        let len = usize::try_from(self.u64()?).ok()?;
        if trust_types::audit_ledger::cap_hit_if(
            len > MAX_CONTEXT_FIELD_BYTES,
            "crates/trust-certify/src/clean_island/ensures_evidence.rs:MAX_CONTEXT_FIELD_BYTES",
        ) {
            return None;
        }
        self.take(len)
    }

    fn string(&mut self) -> Option<String> {
        String::from_utf8(self.field()?.to_vec()).ok()
    }
}

/// Strict decoder: the magic must lead, every count and length is bounded by
/// the input, no byte may trail, and the record must re-encode to exactly the
/// presented bytes (one wire value per record).
fn decode_context(bytes: &[u8]) -> Option<ContextRecord> {
    let mut reader = Reader { bytes: bytes.strip_prefix(CONTEXT_MAGIC)? };
    let self_fn_name = reader.string()?;
    let mut params = Vec::new();
    for _ in 0..reader.count()? {
        params.push((reader.string()?, reader.string()?));
    }
    let mut clauses = Vec::new();
    for _ in 0..reader.count()? {
        let tag = reader.take(1)?[0];
        if tag != ROUTE_TAG_CITED_THEOREM && tag != ROUTE_TAG_ISLAND_DEFEQ {
            return None;
        }
        clauses.push((tag, reader.string()?, reader.string()?));
    }
    let goal = reader.field()?.to_vec();
    let mut environment_digest = [0u8; 32];
    environment_digest.copy_from_slice(reader.take(32)?);
    let dependency_count = reader.u64()?;
    if !reader.bytes.is_empty() || self_fn_name.is_empty() || clauses.is_empty() || goal.is_empty()
    {
        return None;
    }
    let record =
        ContextRecord { self_fn_name, params, clauses, goal, environment_digest, dependency_count };
    (encode_context(&record) == bytes).then_some(record)
}

#[cfg(test)]
mod tests {
    use trust_types::{Formula, SourceSpan, VcKind};

    use super::super::{admit_certified_island_definition, check_clean_island_into};
    use super::*;

    const ISLAND: &str = "def self_dq (x : UInt64) : UInt64 := x\n\n\
         def same_dq (x : UInt64) : UInt64 := x\n\n\
         def diff_dq (x : UInt64) : UInt64 := UInt64.add x 1\n\n\
         theorem ge_refl : forall (x : UInt64), Nat.le (UInt64.toNat x) (UInt64.toNat x) := \
             fun x => @Nat.le.refl (UInt64.toNat x)\n\n\
         theorem nat_refl : forall (n : Nat), Nat.le n n := fun n => @Nat.le.refl n";

    const PARAMS: &[(&str, &str)] = &[("x", "u64")];

    /// Trust (nat-lift): the inputs EVERY compiler discharge lane hands this
    /// site — `ClauseMode::ProofLift` with the contracted function's resolved
    /// return spelling. The pre-existing surfaces below carry no cast, so they
    /// must mint byte-identically under it; that is the corpus control for this
    /// crate's half of the mode change, and it is why these tests were moved
    /// onto `INPUTS` rather than onto `ProofClauseInputs::strict()`.
    static INPUTS: std::sync::LazyLock<trust_spec_elab::ProofClauseInputs> =
        std::sync::LazyLock::new(|| trust_spec_elab::ProofClauseInputs::proof_lift(Some("u64")));

    fn fixture() -> (Environment, trust_spec_elab::FacetTable) {
        let mut env = Environment::with_prelude();
        let outcome = check_clean_island_into(ISLAND, &mut env);
        assert!(!outcome.is_rejected(), "island: {:?}", outcome.errors);
        let mut facets = trust_spec_elab::FacetTable::new();
        for name in ["self_dq", "same_dq", "diff_dq"] {
            admit_certified_island_definition(&env, name, &mut facets)
                .expect("strict kernel definition must be admitted");
        }
        (env, facets)
    }

    fn postcondition_vc(function: &str) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::Postcondition,
            function: trust_types::Symbol::intern(function),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        }
    }

    fn cited<'a>(
        clause_src: &'a str,
        theorem: &'a str,
        facets: &'a trust_spec_elab::FacetTable,
    ) -> EnsuresDischargeClause<'a> {
        EnsuresDischargeClause {
            clause_src,
            route: EnsuresDischargeRoute::CitedTheorem(theorem),
            facets,
        }
    }

    fn defeq<'a>(
        clause_src: &'a str,
        definition: &'a str,
        facets: &'a trust_spec_elab::FacetTable,
    ) -> EnsuresDischargeClause<'a> {
        EnsuresDischargeClause {
            clause_src,
            route: EnsuresDischargeRoute::IslandDefeq(definition),
            facets,
        }
    }

    /// POSITIVE, both routes and their conjunction: the payload mints, has the
    /// shape the publication boundary demands (non-empty term and context,
    /// SHA-256 lineage, no recheck directive), and pairs with its rechecker.
    #[test]
    fn cited_and_defeq_discharges_mint_recheckable_cleancic_evidence() {
        let (env, facets) = fixture();
        let vc = postcondition_vc("self_dq");
        let surfaces: [Vec<EnsuresDischargeClause<'_>>; 3] = [
            vec![cited("result >= x", "ge_refl", &facets)],
            vec![defeq("result == same_dq(x)", "same_dq", &facets)],
            vec![
                defeq("result == same_dq(x)", "same_dq", &facets),
                cited("result >= x", "ge_refl", &facets),
            ],
        ];
        for clauses in &surfaces {
            let certificate = certify_ensures_discharge(&env, clauses, PARAMS, "self_dq", &INPUTS)
                .expect("a kernel-certified discharge must mint its payload");
            let evidence = certificate.evidence_for_row(&vc).expect("row binding");
            // KR0 switch review (C8, C8b): the E9 lane checks the judgment
            // through the reference entry, and the row's payload carries
            // exactly that certificate.
            let reference =
                certificate.reference().expect("the reference entry accepts the E9 judgment");
            assert_eq!(reference.theory_id(), clean_kernel::TheoryId::LeanReferenceV1);
            assert_eq!(crate::reference_certificate_for(&evidence).as_ref(), Some(reference));
            let trust_ir::ProofEvidence::CleanCic { term, context, lineage, kernel_recheck } =
                &evidence
            else {
                panic!("expected CleanCic evidence");
            };
            assert!(!term.is_empty() && !context.is_empty() && kernel_recheck.is_none());
            assert_eq!(lineage.algorithm, trust_ir::ProofDigestAlgorithm::Sha256);
            assert!(!lineage.is_zero());
            assert!(context.starts_with(CONTEXT_MAGIC));
            assert!(audit_presented_ensures_discharge(&env, term, context));
            assert!(
                recheck_ensures_discharge(
                    &env, clauses, PARAMS, "self_dq", &INPUTS, &vc, &evidence
                ),
                "every honest payload must pair with its public rechecker"
            );
            // The exact elaborated goal travels in the payload.
            let record = decode_context(context).expect("canonical context");
            assert_eq!(record.self_fn_name, "self_dq");
            assert_eq!(record.clauses.len(), clauses.len());
            assert!(deserialize_term(&record.goal).is_ok());
        }
    }

    /// CLOSE NEGATIVE TWINS: what the grade routes refuse mints nothing.
    #[test]
    fn a_refused_discharge_mints_no_evidence() {
        let (env, facets) = fixture();
        // Bodies differ: not definitionally equal.
        assert!(
            certify_ensures_discharge(
                &env,
                &[defeq("result == diff_dq(x)", "diff_dq", &facets)],
                PARAMS,
                "self_dq",
                &INPUTS,
            )
            .is_none()
        );
        // Same-shaped theorem over the wrong carrier: statement drift.
        assert!(
            certify_ensures_discharge(
                &env,
                &[cited("result >= x", "nat_refl", &facets)],
                PARAMS,
                "self_dq",
                &INPUTS,
            )
            .is_none()
        );
        // A definition cannot masquerade as a theorem citation, an absent name
        // resolves to nothing, and an absent defeq referent is refused.
        for theorem in ["same_dq", "absent_thm"] {
            assert!(
                certify_ensures_discharge(
                    &env,
                    &[cited("result >= x", theorem, &facets)],
                    PARAMS,
                    "self_dq",
                    &INPUTS,
                )
                .is_none()
            );
        }
        assert!(
            certify_ensures_discharge(
                &env,
                &[defeq("result == same_dq(x)", "absent_def", &facets)],
                PARAMS,
                "self_dq",
                &INPUTS,
            )
            .is_none()
        );
        // Conjunction rule: one refused clause mints nothing for the surface.
        assert!(
            certify_ensures_discharge(
                &env,
                &[
                    cited("result >= x", "ge_refl", &facets),
                    defeq("result == diff_dq(x)", "diff_dq", &facets),
                ],
                PARAMS,
                "self_dq",
                &INPUTS,
            )
            .is_none()
        );
        assert!(certify_ensures_discharge(&env, &[], PARAMS, "self_dq", &INPUTS).is_none());
    }

    /// ADVERSARIAL CONTROLS on an honest payload: every tampered or transplanted
    /// variant must fail the rechecker.
    #[test]
    fn tampered_or_transplanted_evidence_fails_the_recheck() {
        let (env, facets) = fixture();
        let vc = postcondition_vc("self_dq");
        let clauses = [cited("result >= x", "ge_refl", &facets)];
        let certificate =
            certify_ensures_discharge(&env, &clauses, PARAMS, "self_dq", &INPUTS).expect("mint");
        let evidence = certificate.evidence_for_row(&vc).expect("row binding");
        let trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } = evidence.clone()
        else {
            panic!("expected CleanCic evidence");
        };
        let rebuilt = |term: Vec<u8>, context: Vec<u8>, lineage: trust_ir::ProofDigest| {
            trust_ir::ProofEvidence::CleanCic { term, context, lineage, kernel_recheck: None }
        };
        let recheck = |clauses: &[EnsuresDischargeClause<'_>],
                       vc: &VerificationCondition,
                       evidence: &trust_ir::ProofEvidence| {
            recheck_ensures_discharge(&env, clauses, PARAMS, "self_dq", &INPUTS, vc, evidence)
        };
        assert!(recheck(&clauses, &vc, &evidence), "control");

        // (1) a flipped term byte;
        let mut bad_term = term.clone();
        *bad_term.last_mut().expect("non-empty term") ^= 0x01;
        assert!(!recheck(&clauses, &vc, &rebuilt(bad_term.clone(), context.clone(), lineage)));
        assert!(!audit_presented_ensures_discharge(&env, &bad_term, &context));

        // (2) a flipped context byte, and trailing context bytes;
        let mut bad_context = context.clone();
        *bad_context.last_mut().expect("non-empty context") ^= 0x01;
        assert!(!recheck(&clauses, &vc, &rebuilt(term.clone(), bad_context, lineage)));
        let mut padded = context.clone();
        padded.push(0);
        assert!(decode_context(&padded).is_none());
        assert!(!recheck(&clauses, &vc, &rebuilt(term.clone(), padded, lineage)));

        // (3) the proof of a DIFFERENT clause under this clause's context — a
        // genuine kernel proof, of the wrong proposition;
        let other = certify_ensures_discharge(
            &env,
            &[defeq("result == same_dq(x)", "same_dq", &facets)],
            PARAMS,
            "self_dq",
            &INPUTS,
        )
        .expect("mint other");
        assert!(!recheck(&clauses, &vc, &rebuilt(other.term.clone(), context.clone(), lineage)));
        assert!(!audit_presented_ensures_discharge(&env, &other.term, &context));

        // (4) the honest payload presented for a different clause surface;
        assert!(!recheck(&[defeq("result == same_dq(x)", "same_dq", &facets)], &vc, &evidence));

        // (5) the honest payload transplanted onto another row;
        assert!(!recheck(&clauses, &postcondition_vc("other_fn"), &evidence));

        // (6) a violation-refutation-shaped payload (canonical EMPTY context)
        // is not an E9 payload;
        let empty = crate::canonical_empty_context_bytes().expect("canonical context");
        assert!(decode_context(&empty).is_none());
        assert!(!recheck(&clauses, &vc, &rebuilt(term.clone(), empty, lineage)));

        // (7) a recheck directive is not part of this lane's wire form;
        assert!(!recheck(
            &clauses,
            &vc,
            &trust_ir::ProofEvidence::CleanCic {
                term: term.clone(),
                context: context.clone(),
                lineage,
                kernel_recheck: Some(trust_ir::CleanCicKernelRecheck {
                    module: String::new(),
                    theorems: Vec::new(),
                    anchor: String::new(),
                    allowed_axioms: Vec::new(),
                    binding: None,
                }),
            },
        ));

        // (8) a DIFFERENT environment: the same names, a changed definition of
        // the function. The honest payload no longer regenerates.
        let mut env2 = Environment::with_prelude();
        let outcome = check_clean_island_into(
            &ISLAND.replace(
                "def self_dq (x : UInt64) : UInt64 := x",
                "def self_dq (x : UInt64) : UInt64 := UInt64.add x 0",
            ),
            &mut env2,
        );
        assert!(!outcome.is_rejected(), "island 2: {:?}", outcome.errors);
        let mut facets2 = trust_spec_elab::FacetTable::new();
        for name in ["self_dq", "same_dq", "diff_dq"] {
            admit_certified_island_definition(&env2, name, &mut facets2).expect("admit");
        }
        assert!(!recheck_ensures_discharge(
            &env2,
            &[cited("result >= x", "ge_refl", &facets2)],
            PARAMS,
            "self_dq",
            &INPUTS,
            &vc,
            &evidence,
        ));
        assert!(
            !audit_presented_ensures_discharge(&env2, &term, &context),
            "the kernel-environment closure digest must pin the function's definition"
        );
    }

    /// The RECORDED REFERENT is not a free label. The environment-closure digest
    /// opens with the declaration each clause's recorded route names, so a
    /// context that renames the referent — to a constant that does not exist, or
    /// to a real theorem that is not the one whose proof value `term` carries —
    /// fails the environment-only audit.
    ///
    /// The forged payloads are otherwise PERFECT: same term, same goal, same
    /// dependency count, canonically re-encoded, so `decode_context` accepts
    /// them and the kernel audit of `term : goal` still succeeds. Only the
    /// referent section of the digest separates them, which is what makes this
    /// the control for it rather than for the closure.
    #[test]
    fn a_relabelled_referent_fails_the_environment_audit() {
        let (env, facets) = fixture();
        let clauses = [cited("result >= x", "ge_refl", &facets)];
        let certificate =
            certify_ensures_discharge(&env, &clauses, PARAMS, "self_dq", &INPUTS).expect("mint");
        let record = decode_context(&certificate.context).expect("canonical context");
        assert!(
            audit_presented_ensures_discharge(&env, &certificate.term, &certificate.context),
            "control: the honest payload audits"
        );
        for referent in ["absent_thm", "nat_refl"] {
            let mut forged = record.clone();
            forged.clauses = vec![(ROUTE_TAG_CITED_THEOREM, referent.to_string(), {
                let (_, _, clause) = &record.clauses[0];
                clause.clone()
            })];
            let bytes = encode_context(&forged);
            assert_eq!(
                decode_context(&bytes).as_ref(),
                Some(&forged),
                "the forged context is canonical, so only the digest can refuse it"
            );
            assert!(
                !audit_presented_ensures_discharge(&env, &certificate.term, &bytes),
                "a context relabelled to `{referent}` must not audit"
            );
        }
    }

    /// CLOSURE-DIGEST ISOLATION. A twin environment whose reachable definition
    /// is changed in a DEFEQ-PRESERVING way — `same_dq x` becomes
    /// `(fun y => y) x`, which still reduces to `x` — leaves the kernel judgment
    /// itself intact: the presented `term : goal` still type-checks and still
    /// audits clean there. The only thing that separates the two environments is
    /// the closure digest over the declarations' VALUES, so this pins that the
    /// digest, and not the kernel check standing in front of it, is doing the
    /// work.
    #[test]
    fn a_defeq_preserving_environment_change_still_fails_the_closure_digest() {
        let (env, facets) = fixture();
        let clauses = [defeq("result == same_dq(x)", "same_dq", &facets)];
        let certificate =
            certify_ensures_discharge(&env, &clauses, PARAMS, "self_dq", &INPUTS).expect("mint");
        assert!(
            audit_presented_ensures_discharge(&env, &certificate.term, &certificate.context),
            "control: the honest payload audits in its own environment"
        );
        let mut twin = Environment::with_prelude();
        let outcome = check_clean_island_into(
            &ISLAND.replace(
                "def same_dq (x : UInt64) : UInt64 := x",
                "def same_dq (x : UInt64) : UInt64 := (fun (y : UInt64) => y) x",
            ),
            &mut twin,
        );
        assert!(!outcome.is_rejected(), "twin island: {:?}", outcome.errors);
        // The judgment is still good in the twin: only the recorded closure is
        // different. Kernel-check it directly so the assertion below cannot be
        // passing for the boring reason.
        let record = decode_context(&certificate.context).expect("canonical context");
        let goal = deserialize_term(&record.goal).expect("goal");
        let term = deserialize_term(&certificate.term).expect("term");
        assert!(
            twin.audit_certification(&goal, &term).is_certified(),
            "the defeq-preserving twin must still certify the judgment itself"
        );
        assert!(
            !audit_presented_ensures_discharge(&twin, &certificate.term, &certificate.context),
            "the closure digest must refuse a changed reachable declaration"
        );
    }

    /// The payload is a pure function of its inputs (the publication boundary
    /// content-addresses it), and the lineage separates rows.
    #[test]
    fn evidence_is_deterministic_and_row_bound() {
        let (env, facets) = fixture();
        let clauses = [cited("result >= x", "ge_refl", &facets)];
        let first =
            certify_ensures_discharge(&env, &clauses, PARAMS, "self_dq", &INPUTS).expect("mint");
        let second =
            certify_ensures_discharge(&env, &clauses, PARAMS, "self_dq", &INPUTS).expect("mint");
        assert_eq!(first, second);
        let a = first.evidence_for_row(&postcondition_vc("self_dq")).expect("row a");
        let b = first.evidence_for_row(&postcondition_vc("other_fn")).expect("row b");
        assert_eq!(a, second.evidence_for_row(&postcondition_vc("self_dq")).expect("row a again"));
        assert_ne!(a.clean_cic_lineage(), b.clean_cic_lineage());
    }

    /// Trust (nat-lift): THE FIFTH E9 SITE. A clause carrying `as nat` mints
    /// its publishable payload, and so do its UNLIFTED siblings on the same
    /// surface.
    ///
    /// The blast radius is the point. `certify_ensures_discharge` judges the
    /// function's COMPLETE `ensures` surface as one conjunction, so while this
    /// site ran at `ClauseMode::Strict` a single lifted clause returned
    /// `unsupported term shape` here and the whole function minted `None` —
    /// silently, behind `TRUST_E9_DEBUG`, with no verdict change to notice.
    /// Every clause below discharged in the compiler and would have published
    /// nothing.
    #[test]
    fn a_lifted_clause_still_mints_its_certificate() {
        let mut env = Environment::with_prelude();
        let outcome = check_clean_island_into(
            "def self_nl (x : UInt64) : UInt64 := x\n\n\
             def nat_id (n : Nat) : Nat := n",
            &mut env,
        );
        assert!(!outcome.is_rejected(), "island: {:?}", outcome.errors);
        let mut facets = trust_spec_elab::FacetTable::new();
        for name in ["self_nl", "nat_id"] {
            admit_certified_island_definition(&env, name, &mut facets).expect("admit");
        }
        let lifted = defeq("result as nat == nat_id(x as nat)", "nat_id", &facets);
        let unlifted = defeq("result == self_nl(x)", "self_nl", &facets);

        // Control first: the lifted clause is one a compiler lane really
        // discharges, so a `None` below would be about THIS site and not about
        // an unprovable clause.
        assert!(
            matches!(
                super::super::kernel_prove_ensures_by_defeq_in(
                    &env,
                    "result as nat == nat_id(x as nat)",
                    PARAMS,
                    "self_nl",
                    &facets,
                    &INPUTS,
                ),
                super::super::CitationVerdict::KernelStatementMatchCertified
            ),
            "the lifted clause must kernel-discharge, or this test measures the wrong thing"
        );

        let vc = postcondition_vc("self_nl");
        for surface in [
            vec![lifted],
            // The blast radius: one lifted clause used to cost the unlifted
            // sibling its evidence too.
            vec![lifted, unlifted],
            vec![unlifted, lifted],
        ] {
            let certificate = certify_ensures_discharge(&env, &surface, PARAMS, "self_nl", &INPUTS)
                .expect("a lifted surface must mint its publishable payload");
            let evidence = certificate.evidence_for_row(&vc).expect("row binding");
            assert!(recheck_ensures_discharge(
                &env, &surface, PARAMS, "self_nl", &INPUTS, &vc, &evidence
            ));
        }

        // NEGATIVE TWIN, pinned on the reason: at `Strict` — what this site ran
        // at before — the very same surface mints nothing, because the clause
        // does not elaborate at all.
        let strict = trust_spec_elab::ProofClauseInputs::strict();
        assert!(
            certify_ensures_discharge(&env, &[lifted], PARAMS, "self_nl", &strict).is_none(),
            "the mode is what makes the difference here"
        );
        assert!(
            trust_spec_elab::elaborate_ensures_in(
                "result as nat == nat_id(x as nat)",
                PARAMS,
                "self_nl",
                &facets,
                &strict,
            )
            .expect_err("strict refuses a cast")
            .contains("unsupported term shape"),
            "and the reason is the pre-existing one"
        );
    }

    /// Trust (nat-lift): the DISCLOSED BOUND of the fifth site. A clause whose
    /// lift needs the SEEDED signed value model mints no certificate, although
    /// the compiler discharges it — because the producer would judge in a
    /// seeded CLONE whose closure digest `audit_presented_ensures_discharge`,
    /// holding only the environment, cannot re-derive.
    ///
    /// This is a measurement of a capability the lane does NOT have, kept so
    /// the loss is a pinned fact rather than a silent `None`.
    #[test]
    fn a_signed_lifted_clause_mints_no_certificate_and_that_is_the_disclosed_bound() {
        let mut env = Environment::with_prelude();
        let outcome = check_clean_island_into(
            "def self_mx (x : UInt64) (y : BitVec 64) : UInt64 := x\n\n\
             def mix (a : Nat) (b : Int) : Nat := a",
            &mut env,
        );
        assert!(!outcome.is_rejected(), "island: {:?}", outcome.errors);
        let mut facets = trust_spec_elab::FacetTable::new();
        for name in ["self_mx", "mix"] {
            admit_certified_island_definition(&env, name, &mut facets).expect("admit");
        }
        let params: &[(&str, &str)] = &[("x", "u64"), ("y", "i64")];
        let inputs = trust_spec_elab::ProofClauseInputs::proof_lift(Some("u64"));
        let clause = "result as nat == mix(x as nat, y as int)";

        // The clause elaborates, and it declares the seeding obligation that is
        // the whole reason for the bound. Without this assertion the `None`
        // below could be any other mint miss.
        let elaborated =
            trust_spec_elab::elaborate_ensures_in(clause, params, "self_mx", &facets, &inputs)
                .expect("a signed lift elaborates");
        assert_eq!(
            elaborated.required_signed_lift_widths,
            vec![trust_spec_elab::MachineSIntWidth::I64],
            "the bound is about the SEEDED model; without it this test measures nothing"
        );
        // POSITIVE CONTROL: the compiler really discharges this clause, so what
        // is lost below is publishable evidence for a CERTIFIED row.
        assert!(
            matches!(
                super::super::kernel_prove_ensures_by_defeq_in(
                    &env, clause, params, "self_mx", &facets, &inputs,
                ),
                super::super::CitationVerdict::KernelStatementMatchCertified
            ),
            "the clause must kernel-discharge, or this test measures the wrong thing"
        );

        assert!(
            certify_ensures_discharge(
                &env,
                &[defeq(clause, "mix", &facets)],
                params,
                "self_mx",
                &inputs,
            )
            .is_none(),
            "a seeded signed lift must mint nothing rather than an unauditable payload"
        );
        // NEGATIVE TWIN: the very same surface WITHOUT the signed lift mints,
        // so the `None` above is the seeding bound and not the shape.
        let unsigned = "result as nat == mix(x as nat, 0 as int)";
        assert!(
            certify_ensures_discharge(
                &env,
                &[defeq(unsigned, "mix", &facets)],
                params,
                "self_mx",
                &inputs,
            )
            .is_some(),
            "a lift that needs no seeded model must still mint"
        );
    }
}
