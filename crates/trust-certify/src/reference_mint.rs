// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The KR0 switch: every `Certified` payload this crate hands the compiler is
//! re-checked through Clean's fenced reference entry
//! ([`clean_kernel::ReferenceKernel`]), and the compiler's `Certified` mints
//! require the [`ReferenceCertificate`] that check yields (proven-core plan,
//! increment 2, "the KR0 switch").
//!
//! # The fence
//!
//! A [`ReferenceCertificate`] is built in exactly one place,
//! [`ReferenceCertificate::from_accepted`], which CONSUMES a
//! [`clean_kernel::ReferenceAccepted`] token. That token is constructible only
//! inside `clean_kernel::reference`, after the entry checked the term in
//! Lean's reference theory ([`clean_kernel::TheoryId::LeanReferenceV1`]: the
//! fourteen `Nat` literal extensions and the string-literal expansion, in
//! `CleanMode::Constructive`) against a base whose every constant passed the
//! full kernel check and holds no non-Lean expression form. The certificate's
//! fields are private, it has no other constructor and it is neither
//! `Default` nor `Deserialize`, so code outside this crate can hold one only by
//! receiving it from here. The theory a row names is read off the token
//! ([`ReferenceCertificate::wire_theory`]), never parsed from a string.
//!
//! # What is checked, per lane
//!
//! * The violation-refutation lanes ([`crate::certify_vc`]): the payload is a
//!   term `t : False` in a local context of hypotheses, over a carrier base
//!   (Int, or Real's `Rat`) plus one skolem axiom per free variable. The entry
//!   is built ONCE per carrier from the carrier's base environment (no skolems)
//!   and the payload is checked as ONE closed term: every skolem and every
//!   hypothesis is abstracted into a binder, `∀ xs, ∀ hs, False` with value
//!   `λ xs, λ hs, t`. That is the same judgment (a closed inhabitant of the
//!   universal closure exists iff the open term types in the context), checked
//!   with nothing added to the entry, so one reference kernel and one
//!   environment digest serve every certificate of a carrier.
//! * The E9 ensures-discharge lane
//!   ([`crate::clean_island::certify_ensures_discharge`]): the judgment is
//!   already closed (`goal`, `proof`); the entry is built from the island's
//!   environment and the pair is checked with
//!   [`ReferenceKernel::check_closed_term`].
//!
//! # How the certificate reaches the mint
//!
//! The `CleanCic` carrier (`trust_ir::ProofEvidence`) is a pinned first-party
//! type and has no field for it, so a certificate travels beside its payload:
//! [`register`] records it under the payload's lineage digest (which binds the
//! term, the context and the obligation's identity) together with the term and
//! context digests, and [`reference_certificate_for`] returns it only for the
//! exact payload bytes it was registered with. A payload nothing registered
//! (an old row, a hand-built one, one the entry refused) has no certificate,
//! and the compiler mints no `Certified` authority for it.
//!
//! A refusal never turns into an acceptance and never removes a payload: the
//! lane's own kernel re-check still decides whether a `CleanCic` exists; the
//! entry decides only whether it may be called `Certified`.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::{Mutex, OnceLock};

use clean_kernel::expr::ExprFolderOpt;
use clean_kernel::name::Name;
use clean_kernel::{
    EnvDigest, Environment, Expr, FVarId, LevelVec, ReferenceAccepted, ReferenceKernel,
    ReferenceRefusal, TheoryId,
};
use sha2::{Digest, Sha256};

/// What the Clean reference entry accepted, derived from its
/// [`ReferenceAccepted`] token (see the module docs for the fence).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ReferenceCertificate {
    theory_id: TheoryId,
    env_digest: EnvDigest,
    decl_digest: [u8; 32],
}

impl ReferenceCertificate {
    /// The only constructor: consume the entry's token.
    pub(crate) fn from_accepted(token: ReferenceAccepted) -> Self {
        Self {
            theory_id: token.theory_id(),
            env_digest: token.env_digest(),
            decl_digest: token.decl_digest(),
        }
    }

    /// The theory the entry checked in.
    #[must_use]
    pub fn theory_id(&self) -> TheoryId {
        self.theory_id
    }

    /// The environment the entry checked against.
    #[must_use]
    pub fn env_digest(&self) -> EnvDigest {
        self.env_digest
    }

    /// The content digest of the checked closed `(type, value)` pair.
    #[must_use]
    pub fn decl_digest(&self) -> [u8; 32] {
        self.decl_digest
    }

    /// The wire spelling of the theory. `None` for a theory this crate does
    /// not know how to name (`TheoryId` is `#[non_exhaustive]`): such a row
    /// names no theory and is therefore not Certified (fail closed).
    #[must_use]
    pub fn wire_theory(&self) -> Option<trust_types::KernelTheoryId> {
        match self.theory_id {
            TheoryId::LeanReferenceV1 => Some(trust_types::KernelTheoryId::LeanReferenceV1),
            _ => None,
        }
    }

    /// The wire spelling of the environment digest.
    #[must_use]
    pub fn wire_env_digest(&self) -> trust_types::KernelEnvDigest {
        trust_types::KernelEnvDigest(self.env_digest.0)
    }

    /// `evidence` stamped with this certificate's theory and environment, or
    /// `None` when the theory has no wire spelling.
    #[must_use]
    pub fn stamp(
        &self,
        evidence: trust_types::ProofEvidence,
    ) -> Option<trust_types::ProofEvidence> {
        Some(evidence.with_kernel_reference(self.wire_theory()?, self.wire_env_digest()))
    }
}

// ---------------------------------------------------------------------------
// The side table: payload -> certificate.
// ---------------------------------------------------------------------------

/// Most certificates one process records. Past it nothing more is recorded,
/// so a further payload mints no `Certified` authority (fail closed); the
/// bound keeps a pathological compile from growing the table without limit.
const MAX_REGISTERED: usize = 1 << 20;

#[derive(Clone)]
struct Registered {
    term: [u8; 32],
    context: [u8; 32],
    certificate: ReferenceCertificate,
}

fn table() -> &'static Mutex<trust_types::fx::FxHashMap<[u8; 32], Registered>> {
    static TABLE: OnceLock<Mutex<trust_types::fx::FxHashMap<[u8; 32], Registered>>> =
        OnceLock::new();
    TABLE.get_or_init(|| Mutex::new(trust_types::fx::FxHashMap::default()))
}

pub(crate) fn sha256(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}

/// `TRUST_KR0_WITHHOLD_REFERENCE` set (to anything): register nothing, so every
/// payload of the process reads as one the entry refused. A fail-closed
/// measurement seam (it can only take `Certified` away, never grant it), read
/// once per process; the `tests/ui/trust` mint-refusal case's negative revision
/// uses it.
fn withheld() -> bool {
    static WITHHELD: OnceLock<bool> = OnceLock::new();
    *WITHHELD.get_or_init(|| std::env::var_os("TRUST_KR0_WITHHOLD_REFERENCE").is_some())
}

/// Record that the payload `(term, context, lineage)` was accepted by the
/// reference entry as `certificate`.
pub(crate) fn register(
    term: &[u8],
    context: &[u8],
    lineage: &trust_ir::ProofDigest,
    certificate: ReferenceCertificate,
) {
    if withheld() {
        return;
    }
    register_digests(sha256(term), sha256(context), lineage, certificate);
}

/// Record pre-hashed `(term_digest, context_digest)` under `lineage` without
/// re-hashing multi-KB proof payloads on certificate memo hits.
pub(crate) fn register_digests(
    term_digest: [u8; 32],
    context_digest: [u8; 32],
    lineage: &trust_ir::ProofDigest,
    certificate: ReferenceCertificate,
) {
    if withheld() {
        return;
    }
    let entry = Registered { term: term_digest, context: context_digest, certificate };
    if let Ok(mut table) = table().lock()
        && (table.len() < MAX_REGISTERED || table.contains_key(&lineage.bytes))
    {
        table.insert(lineage.bytes, entry);
    }
}

/// Record `evidence` (a `CleanCic`) under `certificate`; any other evidence
/// is ignored.
pub(crate) fn register_evidence(
    evidence: &trust_ir::ProofEvidence,
    certificate: Option<&ReferenceCertificate>,
) {
    if let (Some(certificate), trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. }) =
        (certificate, evidence)
    {
        register(term, context, lineage, certificate.clone());
    }
}

/// The reference-entry certificate for exactly this `CleanCic` payload, or
/// `None` when the entry never accepted these bytes in this process (any
/// other evidence variant, an old or hand-built payload, a payload the entry
/// refused). The compiler's `Certified` mints require `Some`.
#[must_use]
pub fn reference_certificate_for(
    evidence: &trust_ir::ProofEvidence,
) -> Option<ReferenceCertificate> {
    let trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
        return None;
    };
    reference_certificate_for_parts(term, context, lineage)
}

/// Borrow the wire parts so replay need not clone a proof just to look it up.
pub(crate) fn reference_certificate_for_parts(
    term: &[u8],
    context: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> Option<ReferenceCertificate> {
    let table = table().lock().ok()?;
    let entry = table.get(&lineage.bytes)?;
    (entry.term == sha256(term) && entry.context == sha256(context))
        .then(|| entry.certificate.clone())
}

// ---------------------------------------------------------------------------
// The checks.
// ---------------------------------------------------------------------------

/// Why a payload got no certificate (diagnostics and tests only; it never
/// changes a verdict).
#[derive(Debug)]
pub enum ReferenceMiss {
    /// The entry refused the base or the term.
    Refused(ReferenceRefusal),
    /// The base could not be built, or `new` refused it earlier in this
    /// process (the refusal is recorded once, in [`base_refusals`]).
    NoBase,
    /// The term holds a form this module does not close over, or a skolem
    /// the carrier base does not type as expected.
    Unclosable(&'static str),
}

/// Report a miss on stderr when `TRUST_KR0_DEBUG` is set (measurement only;
/// it never changes a verdict).
pub(crate) fn note_miss(lane: &str, miss: &ReferenceMiss) {
    static DEBUG: OnceLock<bool> = OnceLock::new();
    if *DEBUG.get_or_init(|| std::env::var_os("TRUST_KR0_DEBUG").is_some()) {
        eprintln!("TRUST_KR0_DEBUG REFERENCE-MISS lane={lane} {miss:?}");
    }
}

/// The reference entry over a carrier's base environment, built once.
pub(crate) struct CarrierReference {
    kernel: ReferenceKernel,
    skolem_ty: Expr,
}

impl CarrierReference {
    pub(crate) fn env_digest(&self) -> EnvDigest {
        self.kernel.env_digest()
    }
}

fn base_refusal_log() -> &'static Mutex<BTreeMap<&'static str, String>> {
    static LOG: OnceLock<Mutex<BTreeMap<&'static str, String>>> = OnceLock::new();
    LOG.get_or_init(|| Mutex::new(BTreeMap::new()))
}

/// The base refusals recorded so far, by carrier (diagnostics and tests).
#[must_use]
pub fn base_refusals() -> BTreeMap<&'static str, String> {
    base_refusal_log().lock().map(|log| log.clone()).unwrap_or_default()
}

/// Build the entry over `base` for the carrier `label`, recording a refusal.
pub(crate) fn carrier_reference(
    label: &'static str,
    base: Option<&Environment>,
    skolem_ty: Expr,
) -> Option<CarrierReference> {
    let base = base?.clone();
    match ReferenceKernel::new(base) {
        Ok(kernel) => Some(CarrierReference { kernel, skolem_ty }),
        Err(refusal) => {
            note_miss(
                label,
                &ReferenceMiss::Refused(ReferenceRefusal::Admission(refusal.to_string())),
            );
            if let Ok(mut log) = base_refusal_log().lock() {
                log.insert(label, refusal.to_string());
            }
            None
        }
    }
}

/// Replace each skolem constant by its free variable.
struct SkolemToFVar<'a> {
    skolems: &'a HashMap<Name, FVarId>,
}

impl ExprFolderOpt for SkolemToFVar<'_> {
    fn fold_const_opt(&mut self, name: &Name, levels: &LevelVec) -> Option<Expr> {
        if levels.is_empty() { self.skolems.get(name).map(|id| Expr::fvar(*id)) } else { None }
    }
}

/// One local binder to close over, outermost first.
pub(crate) struct ClosedBinder {
    pub id: FVarId,
    pub type_: Expr,
    pub value: Option<Expr>,
    pub bi: clean_kernel::BinderData,
    pub name: Name,
}

/// `(∀ binders, goal, λ binders, term)`, abstracting innermost first. Every
/// binder is value-free (`check_refutation` refuses a `let` binder before
/// calling this: the violation lanes' contexts hold hypotheses only).
fn close_over(binders: &[ClosedBinder], goal: &Expr, term: &Expr) -> (Expr, Expr) {
    let mut ty = goal.clone();
    let mut val = term.clone();
    for binder in binders.iter().rev() {
        let body_ty = ty.abstract_fvar(binder.id);
        let body_val = val.abstract_fvar(binder.id);
        ty = Expr::pi(binder.bi, binder.type_.clone(), body_ty);
        val = Expr::lam(binder.bi, binder.type_.clone(), body_val);
    }
    (ty, val)
}

/// First fresh free-variable id for the skolem binders: above every id the
/// violation lanes use for hypotheses, so the two never meet.
const SKOLEM_FVAR_BASE: u64 = 0x5_0000_0000;

/// Check the violation refutation `term : goal` in `context` (the lane's
/// hypotheses, outermost first) over the carrier entry, with `skolems` the
/// encoded names of the obligation's free variables (each typed by the
/// carrier's skolem type).
pub(crate) fn check_refutation(
    carrier: &CarrierReference,
    skolems: &BTreeSet<String>,
    context: Vec<ClosedBinder>,
    goal: &Expr,
    term: &Expr,
) -> Result<ReferenceCertificate, ReferenceMiss> {
    if context.iter().any(|binder| binder.value.is_some()) {
        // The violation lanes' contexts hold value-free hypotheses only; a
        // `let` binder is a shape this module does not close over.
        return Err(ReferenceMiss::Unclosable("a let binder in the context"));
    }
    let mut skolem_ids: HashMap<Name, FVarId> = HashMap::new();
    let mut binders: Vec<ClosedBinder> = Vec::new();
    for (i, encoded) in skolems.iter().enumerate() {
        let name = Name::from_string(encoded);
        if carrier.kernel.environment().get_const(&name).is_some() {
            // A skolem must be fresh over the base, exactly as `build_env`'s
            // `add_decl` requires; a collision is not this module's to resolve.
            return Err(ReferenceMiss::Unclosable("a skolem names a base constant"));
        }
        let id = FVarId::new(SKOLEM_FVAR_BASE + i as u64);
        if context.iter().any(|binder| binder.id == id) {
            return Err(ReferenceMiss::Unclosable("a hypothesis uses a skolem binder id"));
        }
        skolem_ids.insert(name.clone(), id);
        binders.push(ClosedBinder {
            id,
            type_: carrier.skolem_ty.clone(),
            value: None,
            bi: clean_kernel::BinderInfo::Default.into(),
            name,
        });
    }
    let mut folder = SkolemToFVar { skolems: &skolem_ids };
    for binder in context {
        binders.push(ClosedBinder { type_: binder.type_.fold_opt_or_clone(&mut folder), ..binder });
    }
    let goal = goal.fold_opt_or_clone(&mut folder);
    let term = term.fold_opt_or_clone(&mut folder);
    let (ty, val) = close_over(&binders, &goal, &term);
    if ty.has_fvar_quick() || val.has_fvar_quick() {
        return Err(ReferenceMiss::Unclosable("a free variable outside the context"));
    }
    carrier
        .kernel
        .check_closed_term(&ty, &val)
        .map(ReferenceCertificate::from_accepted)
        .map_err(ReferenceMiss::Refused)
}

/// Check the closed pair `proof : goal` through an entry built from `env`
/// (the E9 lane). Public so the base re-check can be tested from its own test
/// binary; the certificate it returns is registered nowhere, so calling it
/// grants no row anything.
pub fn check_closed_in(
    env: &Environment,
    goal: &Expr,
    proof: &Expr,
) -> Result<ReferenceCertificate, ReferenceMiss> {
    let checked = ReferenceKernel::new(env.clone()).and_then(|kernel| {
        kernel.check_closed_term(goal, proof).map(ReferenceCertificate::from_accepted)
    });
    checked.map_err(|refusal| {
        let miss = ReferenceMiss::Refused(refusal);
        note_miss("e9", &miss);
        miss
    })
}

/// Recheck a registered island declaration, including its stored base body.
/// Citing the constant forces the reference entry's dependencies-first base
/// recheck; checking its type alone would trust its Extended-earned stamp.
/// A zero universe instance triggers that generic base recheck without leaving
/// universe parameters free in the closed wrapper judgment. No certificate is
/// registered in the publication side table by this diagnostic/checking entry.
pub fn check_registered_in(
    env: &Environment,
    name: &Name,
) -> Result<ReferenceCertificate, ReferenceMiss> {
    let kernel = ReferenceKernel::new(env.clone()).map_err(ReferenceMiss::Refused)?;
    check_registered_with(&kernel, name)
}

fn check_registered_with(
    kernel: &ReferenceKernel,
    name: &Name,
) -> Result<ReferenceCertificate, ReferenceMiss> {
    let env = kernel.environment();
    let info = env.get_const(name).ok_or(ReferenceMiss::Unclosable(
        "the registered declaration is absent from the island environment",
    ))?;
    let levels = vec![clean_kernel::Level::zero(); info.level_params.len()];
    let type_ = info.type_.instantiate_level_params_direct(&info.level_params, &levels);
    let value = Expr::const_(name.clone(), levels);
    kernel
        .check_closed_term(&type_, &value)
        .map(ReferenceCertificate::from_accepted)
        .map_err(ReferenceMiss::Refused)
}

#[cfg(test)]
thread_local! {
    static ISLAND_RECHECKS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static ISLAND_ENTRIES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

fn count_island_recheck() {
    #[cfg(test)]
    ISLAND_RECHECKS.with(|count| count.set(count.get() + 1));
}

#[cfg(test)]
pub(crate) fn island_rechecks() -> usize {
    ISLAND_RECHECKS.with(std::cell::Cell::get)
}

#[cfg(test)]
pub(crate) fn island_entries() -> usize {
    ISLAND_ENTRIES.with(std::cell::Cell::get)
}

/// One reference entry over an immutable, completed batch environment. The
/// entry's own base-recheck set serves every declaration in that batch; no
/// process-global verdict memo or independently maintained hash key is used.
pub(crate) struct IslandReference(Result<ReferenceKernel, ReferenceRefusal>);

impl IslandReference {
    pub(crate) fn new(env: &Environment) -> Self {
        #[cfg(test)]
        ISLAND_ENTRIES.with(|count| count.set(count.get() + 1));
        Self(ReferenceKernel::new(env.clone()))
    }

    pub(crate) fn base_error(&self) -> Option<String> {
        self.0.as_ref().err().map(|error| format!("{error:?}"))
    }

    pub(crate) fn check_registered(&self, name: &Name) -> Result<ReferenceCertificate, String> {
        count_island_recheck();
        let kernel = self.0.as_ref().map_err(|error| format!("{error:?}"))?;
        check_registered_with(kernel, name).map_err(|error| format!("{error:?}"))
    }
    pub(crate) fn check_judgment(&self, goal: &Expr, proof: &Expr) -> Result<ReferenceCertificate, String> {
        count_island_recheck();
        let kernel = self.0.as_ref().map_err(|error| format!("{error:?}"))?;
        let mut params = IslandLevelParams::default();
        let _ = goal.fold_opt_or_clone(&mut params);
        let _ = proof.fold_opt_or_clone(&mut params);
        if params.0.is_empty() {
            kernel.check_closed_term(goal, proof)
                .map(ReferenceCertificate::from_accepted)
                .map_err(|error| format!("{error:?}"))
        } else {
            check_island_judgment_in(kernel.environment(), goal, proof)
                .map_err(|error| format!("{error:?}"))
        }
    }

}

#[derive(Default)]
struct IslandLevelParams(Vec<Name>);

impl ExprFolderOpt for IslandLevelParams {
    fn should_descend(&self, expr: &Expr) -> bool {
        expr.has_level_param_quick()
    }

    fn fold_sort_opt(&mut self, level: &clean_kernel::Level) -> Option<Expr> {
        level.collect_params(&mut self.0);
        None
    }

    fn fold_const_opt(&mut self, _: &Name, levels: &LevelVec) -> Option<Expr> {
        for level in levels {
            level.collect_params(&mut self.0);
        }
        None
    }
}

/// Check an original anonymous island judgment, including all its universe
/// parameters. Unlike a named base declaration, it cannot be specialized to
/// universe zero: there is no stored generic base judgment to recheck.
/// The wrapper is added only to the private reference environment, never to
/// the crate or its fact delta, and registers no publication certificate.
pub fn check_island_judgment_in(
    env: &Environment,
    goal: &Expr,
    proof: &Expr,
) -> Result<ReferenceCertificate, ReferenceMiss> {
    let mut params = IslandLevelParams::default();
    let _ = goal.fold_opt_or_clone(&mut params);
    let _ = proof.fold_opt_or_clone(&mut params);
    if params.0.is_empty() {
        return check_closed_in(env, goal, proof);
    }
    let mut kernel = ReferenceKernel::new(env.clone()).map_err(ReferenceMiss::Refused)?;
    let stem = Name::from_string("_trust_island_reference");
    let mut nonce = 0u64;
    let name = loop {
        let candidate = stem.clone().num(nonce);
        let base = kernel.environment();
        if base.get_const(&candidate).is_none()
            && base.get_inductive(&candidate).is_none()
            && base.get_constructor(&candidate).is_none()
            && base.get_recursor(&candidate).is_none()
            && base.get_quot(&candidate).is_none()
        {
            break candidate;
        }
        nonce = nonce.checked_add(1).ok_or(ReferenceMiss::Unclosable(
            "no fresh name for the anonymous judgment's private wrapper",
        ))?;
    };
    kernel
        .add_checked(clean_kernel::Declaration::Definition {
            name,
            level_params: params.0,
            type_: goal.clone(),
            value: proof.clone(),
            is_reducible: false,
        })
        .map(ReferenceCertificate::from_accepted)
        .map_err(ReferenceMiss::Refused)
}

/// The prefix every `certify_memo` key carries: the reference theory's digest
/// and each carrier entry's environment digest (zeros for a carrier whose base
/// the entry refused), so a cached certificate is served only under the
/// theory and environments it was checked in.
pub(crate) fn memo_key_prefix(carriers: &[Option<EnvDigest>]) -> Vec<u8> {
    let mut prefix = Vec::with_capacity(32 * (carriers.len() + 1));
    prefix.extend_from_slice(&TheoryId::LeanReferenceV1.digest());
    for digest in carriers {
        prefix.extend_from_slice(&digest.map_or([0u8; 32], |d| d.0));
    }
    prefix
}

#[cfg(test)]
mod tests {
    use trust_types::{Formula, Sort, SourceSpan, VcKind, VerificationCondition};

    use super::*;

    fn contradiction(name: &str) -> VerificationCondition {
        let x = || Formula::Var(name.to_string(), Sort::Int);
        let zero = || Formula::Int(0);
        VerificationCondition {
            kind: VcKind::Assertion { message: format!("{name} bounded") },
            function: "kr0_reference_mint".into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![
                Formula::Lt(Box::new(x()), Box::new(zero())),
                Formula::Lt(Box::new(zero()), Box::new(x())),
            ]),
            contract_metadata: None,
            obligation: None,
        }
    }

    /// Both carrier bases pass the reference entry's base walk (the
    /// measurement the KR0 switch rests on: a refused base would leave every
    /// certificate of that carrier un-Certified).
    #[test]
    fn both_carrier_bases_pass_the_reference_entry() {
        assert!(crate::Carrier::Int.reference().is_some(), "{:?}", base_refusals());
        assert!(crate::Carrier::Real.reference().is_some(), "{:?}", base_refusals());
        assert!(base_refusals().is_empty(), "{:?}", base_refusals());
    }

    /// Positive: a `certify_vc` payload carries a reference certificate in the
    /// Lean reference theory, against the Int carrier's environment.
    #[test]
    fn a_certify_vc_payload_carries_its_reference_certificate() {
        let evidence = crate::certify_vc(&contradiction("kr0_rm_pos")).expect("certifies");
        let certificate = reference_certificate_for(&evidence).expect("reference-checked");
        assert_eq!(certificate.theory_id(), TheoryId::LeanReferenceV1);
        assert_eq!(certificate.wire_theory(), Some(trust_types::KernelTheoryId::LeanReferenceV1));
        assert_eq!(
            Some(certificate.env_digest()),
            crate::Carrier::Int.reference().map(CarrierReference::env_digest)
        );
        let stamped = certificate
            .stamp(trust_types::ProofEvidence::new(
                trust_types::ReasoningKind::Constructive,
                trust_types::AssuranceLevel::Certified,
            ))
            .expect("stamped");
        assert!(stamped.is_certified());
    }

    /// A memo hit (the same violation under a second identity) restamps the
    /// lineage AND re-registers the certificate under it.
    #[test]
    fn a_memo_hit_is_as_reference_checked_as_the_fresh_run() {
        let first = contradiction("kr0_rm_memo");
        let mut second = first.clone();
        second.function = "kr0_reference_mint_twin".into();
        let a = crate::certify_vc(&first).expect("fresh");
        let b = crate::certify_vc(&second).expect("hit");
        assert_ne!(a, b, "a distinct identity gets a distinct lineage");
        assert_eq!(reference_certificate_for(&a), reference_certificate_for(&b));
        assert!(reference_certificate_for(&b).is_some());
    }

    /// Negative controls: the same payload with a changed term byte or context
    /// byte (lineage kept), and a payload nothing registered, have no
    /// certificate; non-CleanCic evidence has none.
    #[test]
    fn a_payload_the_entry_did_not_accept_has_no_certificate() {
        let evidence = crate::certify_vc(&contradiction("kr0_rm_neg")).expect("certifies");
        let trust_ir::ProofEvidence::CleanCic { term, context, lineage, kernel_recheck } =
            evidence.clone()
        else {
            panic!("CleanCic");
        };
        assert!(reference_certificate_for(&evidence).is_some(), "control");
        let mut bad_term = term.clone();
        *bad_term.last_mut().expect("nonempty") ^= 1;
        let mut bad_context = context.clone();
        *bad_context.last_mut().expect("nonempty") ^= 1;
        for (term, context) in [(bad_term, context.clone()), (term.clone(), bad_context)] {
            let forged = trust_ir::ProofEvidence::CleanCic {
                term,
                context,
                lineage,
                kernel_recheck: kernel_recheck.clone(),
            };
            assert!(reference_certificate_for(&forged).is_none());
        }
        let unseen = trust_ir::ProofEvidence::CleanCic {
            term: vec![1],
            context: vec![2],
            lineage: trust_ir::ProofDigest::sha256_domain("kr0-unseen", &[3]),
            kernel_recheck: None,
        };
        assert!(reference_certificate_for(&unseen).is_none());
    }

    /// The Extended-evidence negative control: a judgment the default
    /// `Extended` kernel accepts, in an environment holding one constant that
    /// was added WITHOUT the full kernel check (`add_decl_structural`, the
    /// shape a structural `.olean` import or stand-in has). The plain checker
    /// accepts `kr0_rm_two = 2 := rfl`; the reference entry refuses the base
    /// (`StructuralProvenance`), so the judgment gets no certificate and could
    /// mint nothing `Certified`. Control: the same judgment over the same
    /// constant added through the checked path is certified.
    #[test]
    fn an_extended_only_judgment_gets_no_reference_certificate() {
        use clean_kernel::{Declaration, Level, TypeChecker};
        let c = |s: &str| Expr::const_(Name::from_string(s), Vec::new());
        let nat = c("Nat");
        let two = Expr::nat_lit(2);
        let goal = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [nat.clone(), c("kr0_rm_two"), two.clone()],
        );
        let proof = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
            [nat.clone(), two.clone()],
        );
        let decl = || Declaration::Definition {
            name: Name::from_string("kr0_rm_two"),
            level_params: vec![],
            type_: nat.clone(),
            value: two.clone(),
            is_reducible: false,
        };
        let mut structural = Environment::with_prelude();
        structural.add_decl_structural(decl()).expect("structural add");
        // Extended accepts the judgment.
        TypeChecker::new(&structural).check_type(&proof, &goal).expect("Extended accepts");
        // The reference entry does not.
        let refused = check_closed_in(&structural, &goal, &proof);
        assert!(
            matches!(
                refused,
                Err(ReferenceMiss::Refused(ReferenceRefusal::StructuralProvenance { .. }))
            ),
            "{refused:?}"
        );
        // Control: the constant added through the checked path.
        let mut checked = Environment::with_prelude();
        checked.add_decl(decl()).expect("checked add");
        let certificate = check_closed_in(&checked, &goal, &proof).expect("reference-checked");
        assert_eq!(certificate.theory_id(), TheoryId::LeanReferenceV1);
    }

    /// KR0 switch review (C10): a Real-carrier (QF_LRA) payload carries a
    /// reference certificate, checked against the Real carrier's environment
    /// (not the Int one). Control: the Int positive above.
    #[test]
    fn a_real_lane_payload_carries_its_reference_certificate() {
        let x = || Formula::Var("kr0_rm_real".to_string(), Sort::Real);
        let zero = || Formula::rat_from_int(0);
        let vc = VerificationCondition {
            formula: Formula::And(vec![
                Formula::Lt(Box::new(x()), Box::new(zero())),
                Formula::Lt(Box::new(zero()), Box::new(x())),
            ]),
            ..contradiction("kr0_rm_real_unused")
        };
        let evidence = crate::certify_vc(&vc).expect("the Real lane certifies");
        let certificate = reference_certificate_for(&evidence).expect("reference-checked");
        let real = crate::Carrier::Real.reference().map(CarrierReference::env_digest);
        let int = crate::Carrier::Int.reference().map(CarrierReference::env_digest);
        assert_eq!(Some(certificate.env_digest()), real);
        assert_ne!(real, int, "the two carriers have distinct environments");
    }

    fn hypothesis(id: u64, type_: Expr) -> ClosedBinder {
        ClosedBinder {
            id: FVarId::new(id),
            type_,
            value: None,
            bi: clean_kernel::BinderInfo::Default.into(),
            name: Name::from_string("kr0_rm_h"),
        }
    }

    /// KR0 switch review (C5, C6, C12): the closing guards. A term naming a
    /// free variable outside its context, a hypothesis on a skolem binder id,
    /// and a `let` binder are each `Unclosable`. Control: the same hypothesis
    /// `h : False` on an ordinary id closes, and `λ x h, h` is accepted.
    #[test]
    fn check_refutation_refuses_what_it_cannot_close() {
        let carrier = crate::Carrier::Int.reference().expect("int base");
        let skolems: BTreeSet<String> = ["kr0_rm_c".to_string()].into_iter().collect();
        let h = |id| hypothesis(id, crate::false_expr());
        let accepted = check_refutation(
            carrier,
            &skolems,
            vec![h(1)],
            &crate::false_expr(),
            &Expr::fvar(FVarId::new(1)),
        );
        assert!(accepted.is_ok(), "control: {accepted:?}");
        let outside = check_refutation(
            carrier,
            &skolems,
            vec![h(1)],
            &crate::false_expr(),
            &Expr::fvar(FVarId::new(2)),
        );
        assert!(
            matches!(
                outside,
                Err(ReferenceMiss::Unclosable("a free variable outside the context"))
            ),
            "{outside:?}"
        );
        let on_skolem_id = check_refutation(
            carrier,
            &skolems,
            vec![h(SKOLEM_FVAR_BASE)],
            &crate::false_expr(),
            &Expr::fvar(FVarId::new(SKOLEM_FVAR_BASE)),
        );
        assert!(
            matches!(
                on_skolem_id,
                Err(ReferenceMiss::Unclosable("a hypothesis uses a skolem binder id"))
            ),
            "{on_skolem_id:?}"
        );
        let with_let = ClosedBinder { value: Some(crate::false_expr()), ..h(1) };
        let with_let = check_refutation(
            carrier,
            &skolems,
            vec![with_let],
            &crate::false_expr(),
            &Expr::fvar(FVarId::new(1)),
        );
        assert!(
            matches!(with_let, Err(ReferenceMiss::Unclosable("a let binder in the context"))),
            "{with_let:?}"
        );
    }

    /// The entry itself refuses a closed term that does not prove its goal,
    /// and a skolem that collides with a base constant: `check_refutation`
    /// turns neither into a certificate.
    #[test]
    fn check_refutation_refuses_a_wrong_term_and_a_colliding_skolem() {
        let carrier = crate::Carrier::Int.reference().expect("int base");
        // `fun (x : Int) => x` does not prove `False`.
        let skolems: BTreeSet<String> = ["kr0_rm_x".to_string()].into_iter().collect();
        let x = Expr::const_(Name::from_string("kr0_rm_x"), Vec::new());
        let refused = check_refutation(carrier, &skolems, Vec::new(), &crate::false_expr(), &x);
        assert!(matches!(refused, Err(ReferenceMiss::Refused(_))), "{refused:?}");
        // A skolem spelled like a base constant is not closed over.
        let colliding: BTreeSet<String> = ["Int".to_string()].into_iter().collect();
        let refused = check_refutation(carrier, &colliding, Vec::new(), &crate::false_expr(), &x);
        assert!(matches!(refused, Err(ReferenceMiss::Unclosable(_))), "{refused:?}");
    }
}
