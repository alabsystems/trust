//! Trust (2026-09-25): the OWNED-CHARGE credit for a transitive Assert-bearing
//! bundled member.
//!
//! ## What `ensure_bundled_member_asserts_exactly_charged` protects
//!
//! Lowering replaces an Assert-bearing bundled member's `Assert`s with a derived
//! `requires`, and the member's private obligations are cleared before the public
//! verifier inventory is sealed. So a member `Assert` is checked ONLY by a
//! caller-side `VcKind::Precondition` row in the public inventory of some verified
//! body. A root's inventory carries such a row only at the root's OWN direct
//! calls. A call from any other bundled member has none there, and unless some
//! other verified body carries it, the `Assert` is charged to nobody — a callee
//! that panics reported panic-free. That is the gate author's
//! `<Wrapping<u8> as Div>::div` canary, reached through a second FOREIGN member.
//!
//! ## The over-refusal this closes
//!
//! Sweep `s03` / sample `i04`: `v.iter().copied().find(|x| x % 2 == 0)`. `x % 2` on
//! a `&u32` calls the foreign `<&u32 as Rem<u32>>::rem`, whose body carries the
//! divide-by-zero `Assert`. In the ROOT's bundle its only call site is inside the
//! local closure, so the root's gate refused it ("no exact direct root call"). But
//! the closure is verified as its OWN root in the same compilation, and there
//! `rem` IS a direct root call: this same gate regenerated the exact
//! `Precondition` row at the closure's call, matched it against the closure's
//! inventory, and the row proved (`2 != 0`) — measured on the snapshot
//! (`0.10.0+g43b8fe6ab`): the closure reports `2 proved … out of 2`, one of them
//! `precondition of <&u32 as core::ops::arith::Rem<u32>>::rem`. The charge was
//! OWNED; the root's gate could not see that.
//!
//! ## The rule
//!
//! A call to an Assert-bearing member `M` from a bundled member `C` other than the
//! root is OWNED only when ALL of the following hold:
//!
//! 1. `C` is LOCAL and does not require monomorphization, on every admitting path
//!    (the ledger composes both fail-closed). `C`'s own root run then verified the
//!    body bundled here — the premise the local-member exemption already rests on.
//! 2. `C`'s own verification, in THIS compilation,
//!    (a) ran this gate with `M` as a direct root callee and matched every exact
//!        caller-side row (recorded only on the gate's success path, as an
//!        [`OwnRootMemberAssertCharge`]);
//!    (b) finished ACCEPTED in the fail-closed lane with no error (the point where
//!        `strict_accepted_fns` is written); and
//!    (c) holds, in its OWN results, every row at each charged (kind, site) at
//!        `Trusted`/`Certified`, with at least one row per distinct charged
//!        formula there ([`charged_rows_statically_proved`]). Those statuses exist
//!        only behind a row-bound authority token (`convert_result`), never a
//!        public label; an unproved `Precondition` is reclassified `Failed`
//!        (`fail_closed_unproved_precondition`), so (b) and (c) agree, and (c) is
//!        checked anyway.
//! 3. `C` has no declared contract, no non-tautological precondition and no
//!    `ADAPTER_YIELD` premise. The row was then proved for EVERY input of `C` —
//!    not under an assumption some caller of `C` owes — so it holds in whatever
//!    context the root reaches `C` from.
//! 4. The charge names `M` by its exact extracted source key AND its
//!    compiler-authenticated `DefId`+substs identity, and the multiset of `C`'s
//!    call sites to `M` in THIS bundle (source spans; every site carrying that
//!    identity; every site's callee key binding exactly one bundled body) equals
//!    the multiset `C`'s own run charged.
//!
//! Every site must be owned — by the root (the pre-existing exact regeneration)
//! or by an owning `C` — or `M` is refused, atomically, as before. A member that
//! no call site reaches keeps the old refusal.
//!
//! ## What stays refused, on purpose
//!
//! * A foreign intermediate (`Wrapping<u8>` canary): not local, no own root run.
//! * A local generic's instance: its own root run is the parameter-erased body.
//! * An owner whose charge row did not prove, or that was not (yet) accepted —
//!   e.g. `C` verified through the cycle-safe snapshot path before its own run
//!   finished. Order-dependence here only ever REFUSES.
//! * An owner that rests on a contract or a modeled premise (rule 3). That is
//!   narrower than the local exemption needs; widening it needs its own argument.

use super::*;

/// One Assert-bearing member that a root's OWN bundle charged exactly, at the
/// root's direct calls, through `ensure_bundled_member_asserts_exactly_charged`.
#[derive(Clone, Debug)]
pub(super) struct OwnRootMemberAssertCharge {
    /// The member's exact extracted source (name, def path, source digest) — the
    /// ledger key, so the charged `Assert` population is this body's.
    pub(super) member: BundledMemberSourceIdentityKey,
    /// The compiler-authenticated identity every charged call carried.
    pub(super) member_identity: trust_types::CalleeIdentity,
    /// The root's direct call sites to the member, as a sorted multiset.
    pub(super) call_sites: Vec<SourceSpan>,
    /// The exact caller-side rows the gate regenerated and matched in the root's
    /// own inventory.
    pub(super) rows: Vec<VerificationCondition>,
}

impl OwnRootMemberAssertCharge {
    pub(super) fn new(
        member: BundledMemberSourceIdentityKey,
        member_identity: trust_types::CalleeIdentity,
        mut call_sites: Vec<SourceSpan>,
        rows: Vec<VerificationCondition>,
    ) -> Self {
        sort_call_sites(&mut call_sites);
        Self { member, member_identity, call_sites, rows }
    }

    fn same_as(&self, other: &Self) -> bool {
        self.member == other.member
            && self.member_identity == other.member_identity
            && self.call_sites == other.call_sites
            && self.rows.len() == other.rows.len()
            && self
                .rows
                .iter()
                .zip(&other.rows)
                .all(|(left, right)| exact_bundled_member_precondition_vc(left, right))
    }
}

fn sort_call_sites(sites: &mut [SourceSpan]) {
    sites.sort_by(|left, right| {
        (left.file.as_str(), left.line_start, left.col_start, left.line_end, left.col_end).cmp(&(
            right.file.as_str(),
            right.line_start,
            right.col_start,
            right.line_end,
            right.col_end,
        ))
    });
}

fn same_charges(left: &[OwnRootMemberAssertCharge], right: &[OwnRootMemberAssertCharge]) -> bool {
    left.len() == right.len() && left.iter().zip(right).all(|(a, b)| a.same_as(b))
}

/// What a bundle knows about a LOCAL member's own verification, for rule 2.
#[derive(Clone, Debug, Default)]
pub(super) enum OwnRootAssertChargeEvidence {
    /// No admitting path attached any (every B-lane and every foreign member).
    #[default]
    NotRecorded,
    /// The member's own run supplies no credit; the reason is diagnostic only.
    Refused(&'static str),
    /// The member's own ACCEPTED run charged, and proved, exactly these.
    Charged(Vec<OwnRootMemberAssertCharge>),
    /// Two admitting paths disagreed. Never credits anything.
    Conflicting,
}

impl OwnRootAssertChargeEvidence {
    /// Fail-closed composition across admitting paths: `Conflicting` absorbs,
    /// then `Refused`; two `Charged` must agree exactly.
    fn compose(&mut self, new: Self) {
        let composed = match (std::mem::take(self), new) {
            (Self::NotRecorded, new) => new,
            (Self::Conflicting, _) | (_, Self::Conflicting) => Self::Conflicting,
            (Self::Refused(reason), _) | (_, Self::Refused(reason)) => Self::Refused(reason),
            (Self::Charged(known), Self::Charged(new)) => {
                if same_charges(&known, &new) {
                    Self::Charged(known)
                } else {
                    Self::Conflicting
                }
            }
            (known @ Self::Charged(_), Self::NotRecorded) => known,
        };
        *self = composed;
    }

    fn describe(&self) -> &'static str {
        match self {
            Self::NotRecorded => "it is not a local body with an own root run in this compilation",
            Self::Refused(reason) => *reason,
            Self::Charged(_) => "its own run charged no exactly-matching call-site multiset",
            Self::Conflicting => "its admitting paths disagreed about its own run's charges",
        }
    }
}

/// Attach the own-root evidence of an already-recorded member. The caller records
/// the member first (`record_bundled_member_source_identity`); an absent entry is
/// an internal ordering error and refuses the bundle.
pub(super) fn attach_own_root_assert_charge_evidence(
    ledger: &mut BundledMemberSourceIdentityLedger,
    member: &trust_types::VerifiableFunction,
    evidence: OwnRootAssertChargeEvidence,
) -> Result<(), String> {
    let key = bundled_member_source_identity_key(member)?;
    let Some(provenance) = ledger.get_mut(&key) else {
        return Err(format!(
            "own-root Assert-charge evidence for `{}` was attached before the member was recorded",
            member.def_path
        ));
    };
    provenance.own_root_assert_charges.compose(evidence);
    Ok(())
}

/// Rule 3, read on the owner's OWN extracted root body.
fn owner_rests_on_no_assumption(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    func: &trust_types::VerifiableFunction,
) -> Result<(), &'static str> {
    if !func.contracts.is_empty()
        || !func.spec.requires.is_empty()
        || func.preconditions.iter().any(|precondition| {
            !trust_ir_bridge::member_precondition_is_integer_param_type_range(func, precondition)
        })
    {
        return Err(
            "it carries a declared contract, so its rows hold only under a precondition its own callers owe",
        );
    }
    if adapter_yield::body_carries_premise(tcx, def_id) {
        return Err(
            "it carries an ADAPTER_YIELD premise, so its rows hold only under a modeled fact",
        );
    }
    // Trust (2026-10-08, review round 82): nor an argument premise (D96, D95/D100).
    if super::argument_premise::body_carries_premise(tcx.sess, def_id) {
        return Err(
            "it carries an argument premise (NOALIAS_MUT_ARGS or REFERENCE_ARG_BOX_VALID), so its \
             rows hold only under an unproved language fact",
        );
    }
    Ok(())
}

/// Rule 2(a): publish what THIS root's own gate charged, keyed by the root's
/// `LocalDefId` — never a rendered path. Called only after the gate succeeded.
/// A second construction of the same root must agree exactly, or the record is
/// poisoned for the rest of the compilation.
pub(super) fn record_pending_own_root_assert_charges<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    func: &trust_types::VerifiableFunction,
    charges: Vec<OwnRootMemberAssertCharge>,
) {
    let ty::InstanceKind::Item(def_id) = body.source.instance else {
        return;
    };
    let Some(local) = def_id.as_local() else {
        return;
    };
    let entry = owner_rests_on_no_assumption(tcx, def_id, func).map(|()| charges);
    with_crate_verification_state(tcx.sess, |state| {
        match state.own_root_assert_charges_pending.get_mut(&local) {
            None => {
                state.own_root_assert_charges_pending.insert(local, entry);
            }
            Some(known) => {
                let agree = match (&*known, &entry) {
                    (Ok(known), Ok(new)) => same_charges(known, new),
                    (Err(known), Err(new)) => known == new,
                    _ => false,
                };
                if !agree {
                    *known = Err("its own bundle constructions disagreed about what they charged");
                }
            }
        }
    });
}

/// Rule 2(c) over one verified body's results: for every source site the charge
/// covers, the owner's results hold at least one row per DISTINCT charged
/// formula there, and EVERY row at that (kind, site) is `Trusted` or `Certified`.
/// Pure, so it is unit-tested without a `TyCtxt`.
pub(super) fn charged_rows_statically_proved(
    charges: &[OwnRootMemberAssertCharge],
    results: &[(VerificationCondition, VerificationResult)],
    dispositions: &IndexVec<ObligationId, TrustDisposition>,
) -> Result<(), &'static str> {
    if results.len() != dispositions.len() {
        return Err("its own results and dispositions are not row-aligned");
    }
    // Rows are joined on (kind, source site) only. Every result here is the
    // owner's own, and the published row is rebuilt from the verifier-api
    // obligation: its `function` is the def path where the regenerated row
    // carries the short name, and its formula may be the reconstructed payload.
    // A join on either would never fire. What makes the weaker join safe: ALL
    // rows at the site must be proved, and there must be at least as many as the
    // charge has DISTINCT formulas there (exact de-duplication never merges two
    // distinct formulas), so a dropped second `requires` cannot hide.
    let rows: Vec<&VerificationCondition> =
        charges.iter().flat_map(|charge| charge.rows.iter()).collect();
    for (index, &row) in rows.iter().enumerate() {
        let same_site = |other: &VerificationCondition| {
            other.kind == row.kind && other.location == row.location
        };
        // Judge each site once, at its first charged row.
        if rows[..index].iter().any(|&earlier| same_site(earlier)) {
            continue;
        }
        let mut distinct: Vec<&Formula> = Vec::new();
        for &other in rows.iter().filter(|&&other| same_site(other)) {
            if !distinct.contains(&&other.formula) {
                distinct.push(&other.formula);
            }
        }
        let mut found = 0usize;
        for (row_index, (vc, _)) in results.iter().enumerate() {
            if !same_site(vc) {
                continue;
            }
            found += 1;
            // Proved for EVERY input of the owner (rule 3), not merely Trusted:
            // a `CallerPropagation` row (Trusted/`Deductive`, the R1 lane) is
            // conditional on a complete caller set, an assumption row
            // (Trusted/`None`) is an assumption, and a `Bounded` row is sound
            // only to its depth — none may own a member's charge. Found by the
            // assert-gate adversarial review (2026-09-25, finding 3); `Deductive`
            // is refused wholesale, which is conservative for any other
            // producer of that strength.
            let proved =
                dispositions.get(ObligationId::from_usize(row_index)).is_some_and(|disposition| {
                    matches!(disposition.status, TrustStatus::Trusted | TrustStatus::Certified)
                        && matches!(
                            disposition.strength,
                            TrustProofStrength::SmtUnsat
                                | TrustProofStrength::Inductive
                                | TrustProofStrength::Ownership
                                | TrustProofStrength::Constructive
                        )
                });
            if !proved {
                return Err(
                    "a charged precondition row is not statically proved in its own results",
                );
            }
        }
        if found < distinct.len() {
            return Err("a charged precondition row is absent from its own results");
        }
    }
    Ok(())
}

/// Rules 2(b)+(c): called at the one point a body's own fail-closed verification
/// is known ACCEPTED (beside `strict_accepted_fns`). Promotes the pending charge
/// record to verified evidence only if every charged row proved.
pub(super) fn promote_own_root_assert_charges<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    artifacts: &VerificationArtifacts,
) {
    let ty::InstanceKind::Item(def_id) = body.source.instance else {
        return;
    };
    let Some(local) = def_id.as_local() else {
        return;
    };
    with_crate_verification_state(tcx.sess, |state| {
        let verified = match state.own_root_assert_charges_pending.get(&local) {
            None => Err("its own bundle recorded no exact member charge"),
            Some(Err(reason)) => Err(*reason),
            Some(Ok(charges)) => charged_rows_statically_proved(
                charges,
                &artifacts.results,
                &artifacts.proof_results.dispositions,
            )
            .map(|()| charges.clone()),
        };
        // A body is published once per compilation; a second publication must
        // agree, or the evidence is withdrawn.
        match state.own_root_assert_charges_verified.get_mut(&local) {
            None => {
                state.own_root_assert_charges_verified.insert(local, verified);
            }
            Some(known) => {
                let agree = match (&*known, &verified) {
                    (Ok(known), Ok(new)) => same_charges(known, new),
                    _ => false,
                };
                if !agree {
                    *known = Err("its own verification was published twice with different charges");
                }
            }
        }
    });
}

/// What a bundle that admits `def_id` as a member may credit to that member's own
/// run. Only a local body that does not require monomorphization can carry
/// evidence; everything else is `NotRecorded`.
pub(super) fn own_root_assert_charge_evidence(
    tcx: TyCtxt<'_>,
    def_id: DefId,
) -> OwnRootAssertChargeEvidence {
    let Some(local) = def_id.as_local() else {
        return OwnRootAssertChargeEvidence::NotRecorded;
    };
    if native_defid_lane_definition_requires_monomorphization(tcx, def_id) {
        return OwnRootAssertChargeEvidence::Refused(
            "its definition requires monomorphization, so its own run verified a different body",
        );
    }
    with_crate_verification_state(tcx.sess, |state| {
        match state.own_root_assert_charges_verified.get(&local) {
            Some(Ok(charges)) => OwnRootAssertChargeEvidence::Charged(charges.clone()),
            Some(Err(reason)) => OwnRootAssertChargeEvidence::Refused(*reason),
            None => OwnRootAssertChargeEvidence::Refused(
                "its own verification has not finished accepted in this compilation",
            ),
        }
    })
}

/// The bundled-member (non-root) call sites of `member`, and whether every one of
/// them is OWNED (rules 1, 2 and 4). `sites` counts exactly what the pre-existing
/// mixed-topology refusal counted: calls from `members[1..]` naming the member or
/// carrying its identity.
pub(super) struct NestedMemberCallOwnership {
    pub(super) sites: usize,
    /// `None` when every site is owned (vacuously when `sites == 0`).
    pub(super) unowned: Option<String>,
}

pub(super) fn nested_member_call_ownership(
    members: &[trust_types::VerifiableFunction],
    member: &trust_types::VerifiableFunction,
    member_key: &BundledMemberSourceIdentityKey,
    member_identity: trust_types::CalleeIdentity,
    member_identities: &BundledMemberSourceIdentityLedger,
    // Trust (VEC-AS-SLICE, 2026-09-25): a site inside std's `Vec` scalar-index
    // forwarder may instead be owned BY FORWARDING (`vec_index_forwarder`). `None`
    // where that credit cannot apply (the forwarder's own call sites).
    forwarded: Option<&vec_index_forwarder::ForwardedBoundsCredit<'_>>,
) -> Result<NestedMemberCallOwnership, String> {
    let names_member = |candidate: &trust_types::VerifiableFunction, callee: &str| {
        candidate.name == callee || candidate.def_path == callee
    };
    let mut sites = 0usize;
    let mut unowned: Option<String> = None;
    for caller in members.iter().skip(1) {
        let caller_sites = caller
            .body
            .blocks
            .iter()
            .filter_map(|block| match &block.terminator {
                trust_types::Terminator::Call { func, callee_identity, span, .. }
                | trust_types::Terminator::TailCall { func, callee_identity, span, .. }
                    if names_member(member, func.as_str())
                        || *callee_identity == Some(member_identity) =>
                {
                    Some((func.as_str(), *callee_identity, span.clone()))
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        if caller_sites.is_empty() {
            continue;
        }
        sites += caller_sites.len();
        if unowned.is_some() {
            continue;
        }
        unowned = caller_sites_unowned_reason(
            members,
            member,
            member_key,
            member_identity,
            member_identities,
            caller,
            &caller_sites,
            names_member,
            forwarded,
        )?;
    }
    Ok(NestedMemberCallOwnership { sites, unowned })
}

fn caller_sites_unowned_reason(
    members: &[trust_types::VerifiableFunction],
    member: &trust_types::VerifiableFunction,
    member_key: &BundledMemberSourceIdentityKey,
    member_identity: trust_types::CalleeIdentity,
    member_identities: &BundledMemberSourceIdentityLedger,
    caller: &trust_types::VerifiableFunction,
    caller_sites: &[(&str, Option<trust_types::CalleeIdentity>, SourceSpan)],
    names_member: impl Fn(&trust_types::VerifiableFunction, &str) -> bool,
    forwarded: Option<&vec_index_forwarder::ForwardedBoundsCredit<'_>>,
) -> Result<Option<String>, String> {
    let refuse =
        |why: &str| Ok(Some(format!("the site(s) in `{}` are not owned: {why}", caller.def_path)));
    // Rule 4, per site: the concrete identity, and a callee key that binds
    // exactly one bundled body (an alias or an ambiguous key binds no body the
    // owner's charge could have named).
    for (callee, identity, _) in caller_sites {
        if *identity != Some(member_identity) {
            return refuse("a call carries no, or a different, compiler-authenticated identity");
        }
        let bound =
            members.iter().skip(1).filter(|candidate| names_member(*candidate, *callee)).count();
        if bound != 1 {
            return refuse("a call's callee key does not bind exactly one bundled body");
        }
    }
    // Rules 1 and 2: the caller's provenance.
    let caller_key = bundled_member_source_identity_key(caller)?;
    let Some(provenance) = member_identities.get(&caller_key) else {
        return refuse("the caller has no compiler-owned provenance in this bundle");
    };
    // Trust (VEC-AS-SLICE, 2026-09-25): a site inside std's `Vec` scalar-index
    // forwarder is owned by FORWARDING when every call of the forwarder is charged
    // (`vec_index_forwarder`, rules 1-4). A forwarder is never also a local owner,
    // so its answer is final either way.
    if let Some(credit) = forwarded
        && let Some(judged) = credit.judge(
            caller,
            &caller_key,
            provenance.vec_index_forwarder.is_forwarder(),
            member,
            member_identity,
        )
    {
        return match judged {
            Ok(()) => Ok(None),
            Err(why) => refuse(&why),
        };
    }
    if !provenance.def_is_local || provenance.def_requires_mono {
        return refuse(
            "the caller is not a local body whose own root run verified this exact body",
        );
    }
    let OwnRootAssertChargeEvidence::Charged(charges) = &provenance.own_root_assert_charges else {
        return refuse(provenance.own_root_assert_charges.describe());
    };
    // Rule 4: exactly one charge for this exact member source and identity, over
    // exactly this call-site multiset.
    let mut matching = charges
        .iter()
        .filter(|charge| &charge.member == member_key && charge.member_identity == member_identity);
    let (Some(charge), None) = (matching.next(), matching.next()) else {
        return refuse(
            "its own run recorded no unique charge for this exact member source and identity",
        );
    };
    let mut here: Vec<SourceSpan> = caller_sites.iter().map(|(_, _, span)| span.clone()).collect();
    sort_call_sites(&mut here);
    if here != charge.call_sites {
        return refuse("its call sites here differ from the sites its own run charged");
    }
    Ok(None)
}
