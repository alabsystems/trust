//! Bounded selection and obligation composition for real StepBy constructors.
//!
//! Selection is NOT a totality decision. Every selected body must still pass
//! the existing call-form identity, monomorphization, source-ledger, lowering,
//! and complete per-source-site charge gates. Iterator advancement is outside
//! this constructor slice.

use super::*;

#[cfg(test)]
mod tests;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum ConstructorMember {
    IteratorStepBy,
    New,
    RangeSetup,
    BlanketIntoIter,
}

impl ConstructorMember {
    /// The role's one spelling: the public inventory's `owner_role` and the
    /// `[STEP_BY_CANDIDATE]` diagnostic trace both read it.
    pub(super) fn label(self) -> &'static str {
        match self {
            ConstructorMember::IteratorStepBy => "iterator-step-by",
            ConstructorMember::New => "step-by-new",
            ConstructorMember::RangeSetup => "range-setup",
            ConstructorMember::BlanketIntoIter => "blanket-into-iter",
        }
    }
}

/// Trust (identity-anchor sweep, 2026-09-28): the `Range` lang item, but only
/// when the crate that owns it is this compiler's own RESIDENT `core`. Every
/// identity in this module is anchored on this one `DefId` (the Range ADT, its
/// crate as "the actual core crate", the `StepBy` path inside that crate), so
/// this is the single place the anchor is authenticated.
///
/// The lang item is a source ATTRIBUTE and rustc refuses a duplicate only when
/// both owners are loaded. In a `#![no_core]` graph the real `core` never is, so
/// a verify-off dependency built as a whole-`core` impostor (crate name `core`,
/// passed as `--extern core=`) OWNED `#[lang = "Range"]`, and with the
/// `Iterator` diagnostic item and a `StepBy` at `iter::adapters::step_by` (which
/// renders `core::iter::adapters::step_by::StepBy` because the crate is NAMED
/// `core`) every conjunct of [`candidate`] held: its panicking PROVIDED
/// `step_by` was classified `IteratorStepBy`. MEASURED on stage-1 `trustc` at
/// `246ceb451e5` plus the `[STEP_BY_CANDIDATE]` trace, without this helper:
/// `role=iterator-step-by` for that impostor under `certify` and `strict`
/// (`tests/ui/trust/step_by_constructor_no_core_range_lang_item_impostor_refuted.rs`).
/// No false proof followed, because the foreign-callee collector's own
/// admission gate (`crate_is_authentic_foundational`, residency-conjoined since
/// 2026-09-28) declined to bundle it; but a TRUE role also exempts a callee
/// from that collector's total-std-iterator decline, so it is a grant input,
/// not a label. Residency ([`trust_mir_extract::is_real_sysroot_crate`], the R2
/// discipline) is the identity; the lang item only says which item it is.
/// Refusal-only: the real `core` is resident in the host, `#![no_std]` and
/// cross-compiled lanes (control:
/// `step_by_constructor_resident_core_keeps_candidate.rs`); a genuine `core`
/// loaded from outside the target library directory (`-Zbuild-std`,
/// `--extern core=`) is declined too, the over-decline
/// `crate_is_compiler_resident_sysroot` already discloses.
fn resident_range_lang_item(tcx: TyCtxt<'_>) -> Option<DefId> {
    tcx.lang_items().range_struct().filter(|range| {
        !range.is_local() && trust_mir_extract::is_real_sysroot_crate(tcx, range.krate)
    })
}

fn integer_range<'tcx>(tcx: TyCtxt<'tcx>, value: Ty<'tcx>) -> bool {
    let ty::Adt(def, args) = value.kind() else { return false };
    if Some(def.did()) != resident_range_lang_item(tcx) {
        return false;
    }
    let mut types = args.types();
    matches!((types.next(), types.next()), (Some(element), None)
        if matches!(element.kind(), ty::Int(_) | ty::Uint(_)))
}

fn step_by_range<'tcx>(tcx: TyCtxt<'tcx>, value: Ty<'tcx>) -> Option<Ty<'tcx>> {
    let ty::Adt(def, args) = value.kind() else { return None };
    let core = resident_range_lang_item(tcx)?.krate;
    if def.did().krate != core
        // `NoTrimmed` alone still follows visible reexports: the real core
        // ADT renders as `std::iter::StepBy` in an ordinary downstream crate.
        // Compare the same definition-path spelling used by the extractor,
        // never a user-facing route to the type. The core DefId anchor above
        // and concrete type/instance checks remain independently required.
        || trust_mir_extract::safe_def_path_str(tcx, def.did())
            != "core::iter::adapters::step_by::StepBy"
    {
        return None;
    }
    let mut types = args.types();
    let (Some(inner), None) = (types.next(), types.next()) else { return None };
    integer_range(tcx, inner).then_some(inner)
}

/// Compiler-owned candidate selection only. Names identify a body within the
/// actual core crate anchored by the Range lang item; they never prove it safe.
/// The ordinary importer must recheck the exact syntactic call-form key against
/// this resolved instance before extracting its source.
///
/// "The actual core crate" is [`resident_range_lang_item`]'s crate: the `Range`
/// lang item's owner AND resident in this compiler's own sysroot, never the lang
/// item alone.
pub(super) fn candidate<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    callee: DefId,
    args: ty::GenericArgs<'tcx>,
) -> Option<ConstructorMember> {
    let range = resident_range_lang_item(tcx)?;
    if range.is_local()
        || callee.krate != range.krate
        || args.has_non_region_param()
        || args.has_non_region_infer()
        || args.has_non_region_placeholders()
    {
        return None;
    }
    let instance = ty::Instance::try_resolve(tcx, typing_env, callee, args).ok()??;
    if !matches!(instance.def, ty::InstanceKind::Item(_))
        || instance.def_id().krate != range.krate
        || instance.args.has_non_region_param()
        || instance.args.has_non_region_infer()
        || instance.args.has_non_region_placeholders()
        || !tcx.is_mir_available(instance.def_id())
    {
        return None;
    }
    let method = tcx.item_name(callee);
    let signature = tcx
        .try_instantiate_and_normalize_erasing_regions(args, typing_env, tcx.fn_sig(callee))
        .ok()?
        .skip_binder();
    let inputs = signature.inputs();
    let output = signature.output();
    let trait_id = tcx.trait_of_assoc(callee);
    if method.as_str() == "step_by"
        && trait_id.is_some_and(|id| tcx.is_diagnostic_item(sym::Iterator, id))
        && instance.def_id() == callee
        && inputs.len() == 2
        && integer_range(tcx, inputs[0])
        && inputs[1] == tcx.types.usize
        && step_by_range(tcx, output) == Some(inputs[0])
    {
        return Some(ConstructorMember::IteratorStepBy);
    }
    if method.as_str() == "new"
        && trait_id.is_none()
        && instance.def_id() == callee
        && inputs.len() == 2
        && integer_range(tcx, inputs[0])
        && inputs[1] == tcx.types.usize
        && step_by_range(tcx, output) == Some(inputs[0])
    {
        let owner = tcx.impl_of_assoc(callee)?;
        let self_ty = tcx.type_of(owner).instantiate(tcx, args).skip_normalization();
        if self_ty == output {
            return Some(ConstructorMember::New);
        }
    }
    if method.as_str() == "setup"
        && trait_id.is_some_and(|id| {
            id.krate == range.krate
                && trust_mir_extract::safe_def_path_str(tcx, id)
                    == "core::iter::adapters::step_by::SpecRangeSetup"
        })
        && inputs.len() == 2
        && integer_range(tcx, inputs[0])
        && inputs[1] == tcx.types.usize
        && output == inputs[0]
    {
        let implementation = tcx.trait_impl_of_assoc(instance.def_id())?;
        let implemented =
            tcx.impl_trait_ref(implementation).instantiate(tcx, instance.args).skip_normalization();
        if Some(implemented.def_id) == trait_id && implemented.self_ty() == inputs[0] {
            return Some(ConstructorMember::RangeSetup);
        }
    }
    if method.as_str() == "into_iter"
        && trait_id.is_some_and(|id| tcx.is_diagnostic_item(sym::IntoIterator, id))
        && inputs.len() == 1
        && output == inputs[0]
        && (integer_range(tcx, output) || step_by_range(tcx, output).is_some())
    {
        let implementation = tcx.trait_impl_of_assoc(instance.def_id())?;
        let generic_self = tcx.type_of(implementation).instantiate_identity().skip_normalization();
        let implemented =
            tcx.impl_trait_ref(implementation).instantiate(tcx, instance.args).skip_normalization();
        // This is the actual blanket `impl<I: Iterator> IntoIterator for I`,
        // not a same-named adapter or a custom concrete conversion.
        if matches!(generic_self.kind(), ty::Param(_))
            && Some(implemented.def_id) == trait_id
            && implemented.self_ty() == inputs[0]
        {
            return Some(ConstructorMember::BlanketIntoIter);
        }
    }
    None
}

/// This fact is compiler-private. The source key binds the extracted body;
/// `no_drop_blocks` comes from `Ty::needs_drop` on that SAME instantiated MIR,
/// never from an extracted ADT's display name or a test fixture's assertion.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ConstructorQualification {
    pub identity: trust_types::CalleeIdentity,
    pub role: ConstructorMember,
    pub no_drop_blocks: Vec<trust_types::BlockId>,
}

pub(super) type ConstructorQualifications =
    FxHashMap<BundledMemberSourceIdentityKey, ConstructorQualification>;

pub(super) fn record_qualification(
    ledger: &mut BundledMemberSourceIdentityLedger,
    member: &trust_types::VerifiableFunction,
    qualification: ConstructorQualification,
) -> Result<(), String> {
    let source = ledger
        .get_mut(&bundled_member_source_identity_key(member)?)
        .ok_or("constructor qualification has no source ledger entry")?;
    if !source.def_is_foreign
        || source.identity != Some(qualification.identity)
        || source.constructor.as_ref().is_some_and(|known| known != &qualification)
    {
        return Err("constructor qualification conflicts with its exact compiler provenance".into());
    }
    source.constructor = Some(qualification);
    Ok(())
}

/// Re-extract the same bounded closure used by the importer, before vcgen
/// constructs its reported call-site preconditions. This supplies NO ensures
/// and no assumed safety. The later kept-module gate independently repeats the
/// analysis and demands exact fresh-VC/public-row reconciliation.
pub(super) fn derived_summary<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: &Body<'tcx>,
    callee_name: &str,
) -> Option<trust_vcgen::FunctionSummary> {
    let mut pending: Vec<_> = native_trust_ir_monomorphic_foreign_callees(
        tcx,
        caller,
        ty::TypingEnv::post_analysis(tcx, caller.source.def_id()),
        None,
    )
    .into_iter()
    .filter(|(_, name, _, role)| name == callee_name && role.is_some())
    .collect();
    if pending.len() != 1 {
        return None;
    }
    let mut members = Vec::new();
    let mut ledger = BundledMemberSourceIdentityLedger::default();
    let mut qualifications = ConstructorQualifications::default();
    let mut seen = FxHashMap::default();
    let mut cursor = 0;
    while let Some((instance, name, identity, role)) = pending.get(cursor).cloned() {
        cursor += 1;
        if cursor > 64 || trust_types::verify_budget::budget_exhausted() {
            return None;
        }
        let (identity, role) = (identity?, role?);
        if let Some(known) = seen.insert(name.clone(), identity) {
            if known != identity {
                return None;
            }
            continue;
        }
        let body = instance
            .try_instantiate_mir_and_normalize_erasing_regions(
                tcx,
                ty::TypingEnv::fully_monomorphized(),
                ty::EarlyBinder::bind(tcx, tcx.instance_mir(instance.def).clone()),
            )
            .ok()?;
        if body.has_non_region_param()
            || body.has_non_region_infer()
            || body.has_non_region_placeholders()
        {
            return None;
        }
        // The selector declines authored foreign contracts; preserve the exact
        // extraction recipe anyway, so a future recipe change cannot erase one.
        let contracts = native_bundle_foreign_contract_bundle(tcx, &body).ok()?;
        let mut member = trust_mir_extract::extract_function_with_contract_bundle(
            tcx,
            &body,
            contracts.as_ref(),
        );
        member.name = name.clone();
        member.def_path = name;
        // Trust (2026-10-02): one source identity key for the qualification, the ledger
        // write and the insert below (`member_source_identity_scope`).
        let member_keys =
            member_source_identity_scope::MemberKeyScope::new(std::slice::from_ref(&member));
        let qualification =
            qualify_instantiated_member(tcx, &body, &member, identity, role).ok()?;
        // Trust (generics, 2026-09-13): `def_is_local` is already `false` here — this
        // is the private constructor-analysis queue over INSTANTIATED members — so the
        // Assert-charging exemption cannot fire for these rows whatever the
        // monomorphization flag says. Pass `false` rather than computing it: this
        // ledger never reaches that gate, and a computed value would imply it does.
        // Trust (2026-09-29): the same reasoning for the authenticity flag — this
        // ledger never reaches the runtime-checked disposition, so `false`.
        record_bundled_member_source_identity(
            &mut ledger,
            &member,
            Some(identity),
            false,
            false,
            false,
            false,
        )
        .ok()?;
        qualifications.insert(bundled_member_source_identity_key(&member).ok()?, qualification);
        drop(member_keys);
        // This is the private constructor-analysis queue, not the real module
        // importer. Ordinary collection also offers panic machinery, which has
        // no constructor role. Its target-less call is already a required
        // guarded-false source site; trying to qualify the handler as a
        // constructor would discard the entire caller summary above.
        //
        // Filtering is not an absent-body exemption: plan_for_member below
        // re-reads every remaining call site and requires its present, uniquely
        // identified, qualified body. A returning panic call or any other
        // unqualified call therefore still refuses the whole summary.
        pending.extend(
            native_trust_ir_monomorphic_foreign_callees(
                tcx,
                &body,
                ty::TypingEnv::fully_monomorphized(),
                None,
            )
            .into_iter()
            .filter(|(_, _, _, role)| role.is_some()),
        );
        members.push(member);
    }
    // Trust (2026-10-02): the plan asks every member's key once per visit and once per
    // parent; each is computed at most once while `member_keys` lives.
    let member_keys = member_source_identity_scope::MemberKeyScope::new(&members);
    let entry = members.first()?;
    let summary = plan_for_member(entry, &members, &ledger, &qualifications).ok()?.summary(entry);
    drop(member_keys);
    summary.ok()
}

/// Derive the cleanup fact from the actual compiler type, and bind it to the
/// precise extraction consumed by the plan. This does not select a constructor
/// instance: the caller must obtain `role` from `candidate` at its syntactic
/// call site, after the ordinary monomorphic collector's identity gate.
pub(super) fn qualify_instantiated_member<'tcx>(
    tcx: TyCtxt<'tcx>,
    mono_body: &Body<'tcx>,
    member: &trust_types::VerifiableFunction,
    identity: trust_types::CalleeIdentity,
    role: ConstructorMember,
) -> Result<ConstructorQualification, String> {
    if mono_body.has_non_region_param()
        || mono_body.has_non_region_infer()
        || mono_body.has_non_region_placeholders()
    {
        return Err("constructor cleanup qualification requires a fully instantiated body".into());
    }
    let mut extracted =
        trust_mir_extract::extract_function_with_contract_bundle(tcx, mono_body, None);
    extracted.name = member.name.clone();
    extracted.def_path = member.def_path.clone();
    if bundled_member_source_identity_key(&extracted)?
        != bundled_member_source_identity_key(member)?
    {
        return Err("constructor qualification body differs from the consumed extraction".into());
    }
    let mut no_drop_blocks = Vec::new();
    for (block, data) in mono_body.basic_blocks.iter_enumerated() {
        if let TerminatorKind::Drop { place, .. } = &data.terminator().kind {
            let dropped = place.ty(&mono_body.local_decls, tcx).ty;
            if dropped.needs_drop(tcx, ty::TypingEnv::fully_monomorphized()) {
                return Err("constructor cleanup requires real destructor semantics beyond this no-drop slice".into());
            }
            no_drop_blocks.push(trust_types::BlockId(block.as_usize()));
        }
    }
    Ok(ConstructorQualification { identity, role, no_drop_blocks })
}

#[derive(Clone, Debug)]
pub(super) enum ConstructorSourceSite {
    Safety(trust_ir_bridge::BundledConstructorSafetySite),
    NoDrop { block: trust_types::BlockId, span: trust_types::SourceSpan, place: trust_types::Place },
}

#[derive(Clone, Debug)]
pub(super) struct ConstructorCallPathEdge {
    pub caller_name: String,
    pub caller_def_path: String,
    pub caller_source_digest: String,
    pub callee_source_digest: String,
    pub call: trust_ir_bridge::BundledConstructorCallSite,
}

/// One source site along ONE invocation path. Safety checks and compiler
/// dispositions remain distinct: needs_drop=false has NO verification predicate
/// and cannot inflate the public proof-obligation inventory.
#[derive(Clone, Debug)]
pub(super) struct ConstructorSiteRequirement {
    pub owner_name: String,
    pub owner_def_path: String,
    pub owner_source_digest: String,
    pub owner_identity: trust_types::CalleeIdentity,
    pub owner_role: ConstructorMember,
    pub source: ConstructorSourceSite,
    pub path: Vec<ConstructorCallPathEdge>,
    pub requirement: Option<Formula>,
}

impl ConstructorSiteRequirement {
    /// Canonical inventory payload uses the compiler crate's existing JSON
    /// dependency. No serialized payload can create a qualification: these
    /// records are emitted only from the independently reconstructed plan.
    pub(super) fn to_json(&self) -> serde_json::Value {
        let source = match &self.source {
            ConstructorSourceSite::Safety(site) => serde_json::json!({
                "kind": "mir-safety-site", "site": site,
            }),
            ConstructorSourceSite::NoDrop { block, span, place } => serde_json::json!({
                "kind": "compiler-no-drop-site", "block": block, "span": span, "place": place,
                "disposition": "needs-drop-false", "proof_credit": false,
            }),
        };
        let path: Vec<_> = self
            .path
            .iter()
            .map(|edge| {
                serde_json::json!({
                    "caller_name": edge.caller_name,
                    "caller_def_path": edge.caller_def_path,
                    "caller_source_digest": edge.caller_source_digest,
                    "callee_source_digest": edge.callee_source_digest,
                    "call": edge.call,
                })
            })
            .collect();
        serde_json::json!({
            "schema": "trustc.constructor-source-site-requirement.v1",
            "owner_name": self.owner_name,
            "owner_def_path": self.owner_def_path,
            "owner_source_digest": self.owner_source_digest,
            "owner_identity": self.owner_identity,
            "owner_role": self.owner_role.label(),
            "source": source,
            "path": path,
            "requirement": self.requirement,
        })
    }
}

#[derive(Clone, Debug)]
pub(super) struct ConstructorPlan {
    pub entry: BundledMemberSourceIdentityKey,
    pub entry_identity: trust_types::CalleeIdentity,
    pub sites: Vec<ConstructorSiteRequirement>,
    pub members: FxHashSet<BundledMemberSourceIdentityKey>,
}

/// A source site's obligation instantiated at one exact ROOT invocation. The
/// nested guards live in `site.requirement`; caller guards/SSA/own requires are
/// supplied by the actual vcgen callsite implementation, not re-invented here.
#[derive(Clone, Debug)]
pub(super) struct ConstructorRootCharge {
    pub root_source_digest: String,
    pub root_block: trust_types::BlockId,
    pub root_identity: trust_types::CalleeIdentity,
    pub root_arguments: Vec<trust_types::Operand>,
    pub site: ConstructorSiteRequirement,
    pub vc: VerificationCondition,
}

pub(super) const CONSTRUCTOR_SOURCE_SITE_METADATA: &str = "trust.constructor.source_site.v1";

/// Why [`reconcile_bundle`] refuses a constructor reconciliation whose caller-side
/// regeneration the ambient per-function budget tripped during.
pub(super) const CONSTRUCTOR_REGENERATION_OVER_BUDGET: &str = "constructor root-charge \
     regeneration ran past the per-function verification budget; its rows are discarded, \
     never charged";
pub(super) const CONSTRUCTOR_SOURCE_INVENTORY_METADATA: &str =
    "trust.constructor.source_inventory.v1";

#[derive(Clone, Debug)]
pub(super) struct ConstructorPublicCharge {
    pub obligation_index: usize,
    pub obligation_id: String,
    pub vc_index: usize,
    pub source_site_payload: String,
    expected_public_row: String,
}

pub(super) struct ConstructorBundleBindings {
    pub members: FxHashSet<BundledMemberSourceIdentityKey>,
    charges: Vec<ConstructorPublicCharge>,
    inventory_payload: Option<String>,
}

impl ConstructorBundleBindings {
    pub(super) fn attach(
        self,
        bundle: &mut trust_verifier_api::TrustContractBundle,
    ) -> Result<(), String> {
        // Validate the entire target population first; attachment is atomic.
        for charge in &self.charges {
            if bundle.obligations.get(charge.obligation_index).is_none_or(|row| {
                row.obligation_id != charge.obligation_id
                    || serde_json::to_string(row).ok().as_ref() != Some(&charge.expected_public_row)
            }) {
                return Err("constructor public inventory changed after reconciliation".into());
            }
        }
        for charge in self.charges {
            let row = &mut bundle.obligations[charge.obligation_index];
            if !row.metadata.iter().any(|entry| entry.key == CONSTRUCTOR_SOURCE_SITE_METADATA) {
                row.metadata.push(trust_verifier_api::MetadataEntry {
                    key: CONSTRUCTOR_SOURCE_SITE_METADATA.into(),
                    value: charge.source_site_payload,
                });
            }
            if let Some(value) = &self.inventory_payload
                && !row
                    .metadata
                    .iter()
                    .any(|entry| entry.key == CONSTRUCTOR_SOURCE_INVENTORY_METADATA)
            {
                row.metadata.push(trust_verifier_api::MetadataEntry {
                    key: CONSTRUCTOR_SOURCE_INVENTORY_METADATA.into(),
                    value: value.clone(),
                });
            }
        }
        Ok(())
    }
}

/// Only this complete kept-source/entry-path/public-row reconciliation may
/// exempt a selected constructor member from the legacy direct-entry gate.
pub(super) fn reconcile_bundle(
    root: &trust_types::VerifiableFunction,
    members: &[trust_types::VerifiableFunction],
    ledger: &BundledMemberSourceIdentityLedger,
    all_vcs: &[VerificationCondition],
    bundle: &trust_verifier_api::TrustContractBundle,
) -> Result<ConstructorBundleBindings, String> {
    let mut qualifications = ConstructorQualifications::default();
    for member in members.iter().skip(1) {
        let key = bundled_member_source_identity_key(member)?;
        if let Some(qualification) = ledger.get(&key).and_then(|source| source.constructor.clone())
        {
            qualifications.insert(key, qualification);
        }
    }
    if qualifications.is_empty() {
        return Ok(ConstructorBundleBindings {
            members: FxHashSet::default(),
            charges: Vec::new(),
            inventory_payload: None,
        });
    }
    let mut covered = FxHashSet::default();
    let mut charges = Vec::new();
    let mut inventory = Vec::new();
    let mut planned = Vec::new();
    for entry in members.iter().skip(1) {
        let key = bundled_member_source_identity_key(entry)?;
        if !qualifications.contains_key(&key) {
            continue;
        }
        let direct = root.body.blocks.iter().any(|block| matches!(&block.terminator,
            trust_types::Terminator::Call { func, .. } | trust_types::Terminator::TailCall { func, .. }
                if func == &entry.name || func == &entry.def_path));
        if direct {
            let plan = plan_for_member(entry, &members[1..], ledger, &qualifications)?;
            for (block, arguments, span, site) in plan.root_sites(root)? {
                inventory.push(serde_json::json!({
                    "root_block": block, "root_call_span": span, "root_arguments": arguments,
                    "root_call_identity": plan.entry_identity,
                    "requires_public_vc": site.requirement.is_some(), "source_site": site.to_json(),
                }));
            }
            let database = plan.charge_database(entry)?;
            planned.push((plan, database));
        }
    }
    // Trust: 2026-10-17 (gate-rca deadline, B class) — ONE caller-side regeneration of
    // the root for every directly called member: the root's whole-body analyses (its
    // two-pass path-definition fixpoint above all) are computed once, not once per
    // member (`trust_vcgen::generate_callsite_precondition_vcs_for_each`; element `i` is
    // exactly the single-database producer's answer for member `i`). Then the consumer
    // discipline of `trust_types::verify_budget`: a regeneration the ambient budget
    // tripped during (or a deadline already passed) is discarded, never charged.
    let databases: Vec<&trust_vcgen::SummaryDatabase> =
        planned.iter().map(|(_, database)| database).collect();
    let regenerated = trust_vcgen::generate_callsite_precondition_vcs_for_each(root, &databases);
    if trust_types::verify_budget::exhausted_readonly() {
        return Err(CONSTRUCTOR_REGENERATION_OVER_BUDGET.into());
    }
    for ((plan, _), vcs) in planned.into_iter().zip(regenerated) {
        charges.extend(plan.root_charges_from(root, vcs)?);
        // A set extended from a set holds the same members in any visit order.
        #[allow(rustc::potential_query_instability)]
        covered.extend(plan.members);
    }
    // `any` over membership tests answers the same in any visit order.
    #[allow(rustc::potential_query_instability)]
    if covered.len() != qualifications.len()
        || qualifications.keys().any(|key| !covered.contains(key))
    {
        return Err("constructor member has no complete exact root invocation path".into());
    }
    // The `any` below is a pure predicate, which answers the same in any visit order.
    #[allow(rustc::potential_query_instability)]
    for member in members.iter().skip(1) {
        if covered.contains(&bundled_member_source_identity_key(member)?) {
            continue;
        }
        for block in &member.body.blocks {
            if let trust_types::Terminator::Call { func, callee_identity, .. }
            | trust_types::Terminator::TailCall { func, callee_identity, .. } = &block.terminator
            {
                if qualifications.iter().any(|(key, qualification)| {
                    key.name == *func
                        || key.def_path == *func
                        || Some(qualification.identity) == *callee_identity
                }) {
                    return Err("constructor has an uncharged invocation from outside its exact root closure".into());
                }
            }
        }
    }
    let public = bind_public_root_charges(root, &charges, all_vcs, bundle)?;
    if public.is_empty() && !inventory.is_empty() {
        return Err("constructor dispositions have no existing required safety carrier".into());
    }
    let public_links: Vec<_> = public
        .iter()
        .map(|charge| {
            serde_json::json!({
                "obligation_id": charge.obligation_id, "vc_index": charge.vc_index,
                "source_site_payload": charge.source_site_payload,
            })
        })
        .collect();
    let member_keys: Vec<_> =
        members
            .iter()
            .filter_map(|member| {
                let key = bundled_member_source_identity_key(member).ok()?;
                covered.contains(&key).then(|| serde_json::json!({
            "name": key.name, "def_path": key.def_path, "source_digest": key.source_digest,
        }))
            })
            .collect();
    let payload = serde_json::to_string(&serde_json::json!({
        "schema": CONSTRUCTOR_SOURCE_INVENTORY_METADATA,
        "root_source_digest": compiler_function_source_digest_hex(root)?,
        "members": member_keys, "source_sites": inventory, "public_safety_charges": public_links,
    }))
    .map_err(|error| error.to_string())?;
    // Carry the complete disposition inventory on existing required safety
    // rows, never as a new proof obligation or a new bundle-wide assumption
    // key. The existing full public-row snapshot binds these exact bytes.
    for charge in &public {
        let metadata = &bundle.obligations[charge.obligation_index].metadata;
        if !metadata_has_exact_optional_value(
            metadata,
            CONSTRUCTOR_SOURCE_INVENTORY_METADATA,
            metadata
                .iter()
                .any(|entry| entry.key == CONSTRUCTOR_SOURCE_INVENTORY_METADATA)
                .then_some(payload.as_str()),
        ) {
            return Err(
                "constructor source/disposition inventory differs from fresh reconstruction".into(),
            );
        }
    }
    Ok(ConstructorBundleBindings {
        members: covered,
        charges: public,
        inventory_payload: Some(payload),
    })
}

/// Bind an independently reconstructed, complete source-site population to the
/// compiler's exact fresh VC carrier AND its public obligation IDs. This is a
/// reconciliation result, not a proof. It must run before private bridge rows
/// are cleared, and a caller may attach these payloads only after every member
/// in the proposed constructor closure is covered.
pub(super) fn bind_public_root_charges(
    root: &trust_types::VerifiableFunction,
    charges: &[ConstructorRootCharge],
    all_vcs: &[VerificationCondition],
    bundle: &trust_verifier_api::TrustContractBundle,
) -> Result<Vec<ConstructorPublicCharge>, String> {
    let crate_name = match &bundle.subject {
        trust_verifier_api::BundleSubject::Function { crate_name, path }
            if !crate_name.trim().is_empty() && path == &root.def_path =>
        {
            crate_name
        }
        _ => return Err("constructor charges have no exact function bundle subject".into()),
    };
    let source_digest = compiler_function_source_digest_hex(root)?;
    // Public VC IDs use the extractor's RAW canonical-source digest. Internal
    // provenance uses the separate domain-framed compiler digest above.
    let public_source_digest = trust_mir_extract::verifier_source_digest(root);
    let mut callees = FxHashSet::default();
    for charge in charges {
        let VcKind::Precondition { callee } = &charge.vc.kind else {
            return Err("constructor source site is not a reported precondition".into());
        };
        if charge.root_source_digest != source_digest {
            return Err("constructor charge belongs to another root source snapshot".into());
        }
        callees.insert(callee.as_str());
    }
    let actual: Vec<_> = all_vcs.iter().enumerate().filter(|(_, vc)| {
        (vc.function.as_str() == root.name || vc.function.as_str() == root.def_path)
            && matches!(&vc.kind, VcKind::Precondition { callee } if callees.contains(callee.as_str()))
    }).collect();
    if actual.len() != charges.len() {
        return Err("constructor public source-site and fresh-VC counts differ".into());
    }
    let public_indices: Vec<_> = bundle
        .obligations
        .iter()
        .map(|obligation| {
            exact_fresh_vc_index_for_obligation_with_source_digest_and_crate_name(
                root,
                obligation,
                all_vcs,
                &public_source_digest,
                Some(crate_name),
            )
        })
        .collect();
    let mut consumed = vec![false; actual.len()];
    let mut public_ids = FxHashSet::default();
    let mut bindings = Vec::new();
    for charge in charges {
        let position = actual
            .iter()
            .enumerate()
            .position(|(position, (_, vc))| {
                !consumed[position] && exact_bundled_member_precondition_vc(&charge.vc, vc)
            })
            .ok_or("constructor source-site formula or provenance is missing from fresh VCs")?;
        consumed[position] = true;
        let (vc_index, _) = actual[position];
        let matches: Vec<_> = public_indices
            .iter()
            .enumerate()
            .filter_map(|(index, actual)| (*actual == Some(vc_index)).then_some(index))
            .collect();
        let [obligation_index] = matches.as_slice() else {
            return Err(
                "constructor source-site VC has missing or duplicate authenticated public rows"
                    .into(),
            );
        };
        let obligation = &bundle.obligations[*obligation_index];
        if !public_ids.insert(obligation.obligation_id.clone())
            || bundle
                .obligations
                .iter()
                .filter(|row| row.obligation_id == obligation.obligation_id)
                .count()
                != 1
        {
            return Err("constructor public obligation identity is not unique".into());
        }
        let payload = serde_json::to_string(&serde_json::json!({
            "schema": CONSTRUCTOR_SOURCE_SITE_METADATA,
            "root_source_digest": charge.root_source_digest,
            "root_block": charge.root_block,
            "root_call_identity": charge.root_identity,
            "root_arguments": charge.root_arguments,
            "source_site": charge.site.to_json(),
            "caller_vc_index": vc_index,
            "caller_formula": charge.vc.formula,
            "public_obligation_id": obligation.obligation_id,
        }))
        .map_err(|error| error.to_string())?;
        // A supplied payload is never its own authority. Missing is allowed
        // during first compiler mint; duplicates or different bytes refuse.
        if !metadata_has_exact_optional_value(
            &obligation.metadata,
            CONSTRUCTOR_SOURCE_SITE_METADATA,
            obligation
                .metadata
                .iter()
                .any(|entry| entry.key == CONSTRUCTOR_SOURCE_SITE_METADATA)
                .then_some(payload.as_str()),
        ) {
            return Err(
                "constructor public source-site metadata differs from fresh reconstruction".into(),
            );
        }
        bindings.push(ConstructorPublicCharge {
            obligation_index: *obligation_index,
            obligation_id: obligation.obligation_id.clone(),
            vc_index,
            source_site_payload: payload,
            expected_public_row: serde_json::to_string(obligation)
                .map_err(|error| error.to_string())?,
        });
    }
    Ok(bindings)
}

impl ConstructorPlan {
    pub(super) fn summary(
        &self,
        entry: &trust_types::VerifiableFunction,
    ) -> Result<trust_vcgen::FunctionSummary, String> {
        if bundled_member_source_identity_key(entry)? != self.entry {
            return Err("constructor summary entry differs from the analyzed source".into());
        }
        let types = (1..=entry.body.arg_count)
            .map(|index| {
                entry
                    .body
                    .locals
                    .iter()
                    .find(|local| local.index == index)
                    .map(|local| local.ty.clone())
                    .ok_or("constructor formal type missing".to_string())
            })
            .collect::<Result<Vec<_>, _>>()?;
        let mut summary = trust_vcgen::FunctionSummary::new(entry.name.clone())
            .with_param_names(trust_ir_bridge::bundled_constructor_formal_names(entry))
            .with_param_types(types);
        for site in &self.sites {
            if let Some(requirement) = &site.requirement {
                summary = summary.with_precondition(requirement.clone());
            }
        }
        Ok(summary)
    }

    /// [`Self::root_charges_from`] of the root's single-database regeneration (the
    /// production reconciliation regenerates every member's database in one batch).
    #[cfg(test)]
    pub(super) fn root_charges(
        &self,
        root: &trust_types::VerifiableFunction,
        entry: &trust_types::VerifiableFunction,
    ) -> Result<Vec<ConstructorRootCharge>, String> {
        let db = self.charge_database(entry)?;
        self.root_charges_from(root, trust_vcgen::generate_callsite_precondition_vcs(root, &db))
    }

    /// The one-summary database whose caller-side regeneration of the root charges this
    /// plan's sites ([`Self::root_charges_from`]).
    pub(super) fn charge_database(
        &self,
        entry: &trust_types::VerifiableFunction,
    ) -> Result<trust_vcgen::SummaryDatabase, String> {
        let mut db = trust_vcgen::SummaryDatabase::new();
        db.insert(self.summary(entry)?);
        Ok(db)
    }

    /// The charges of this plan's sites, from `vcs`: the root's caller-side regeneration
    /// under [`Self::charge_database`].
    ///
    /// Cardinality is checked against the independent source-site population,
    /// not inferred from however many rows vcgen happened to retain. A future
    /// structural pruning change therefore refuses this import instead of
    /// deleting a born safety obligation. No-drop dispositions are not proof
    /// obligations. Current genuine entry-guard implications
    /// are outside the interval-only F5 pruning grammar.
    pub(super) fn root_charges_from(
        &self,
        root: &trust_types::VerifiableFunction,
        vcs: Vec<VerificationCondition>,
    ) -> Result<Vec<ConstructorRootCharge>, String> {
        let origins: Vec<_> = self
            .root_sites(root)?
            .into_iter()
            .filter(|(_, _, _, site)| site.requirement.is_some())
            .collect();
        if origins.len() != vcs.len() {
            return Err(format!(
                "constructor root source-site charge count mismatch: expected {}, generated {}",
                origins.len(),
                vcs.len()
            ));
        }
        let root_source_digest = compiler_function_source_digest_hex(root)?;
        origins.into_iter().zip(vcs).map(|((block, arguments, span, site), vc)| {
            if vc.function.as_str() != root.name || vc.location != span
                || !matches!(&vc.kind, VcKind::Precondition { callee } if callee == &self.entry.name) {
                return Err("constructor source-site charge order or caller provenance mismatch".into());
            }
            Ok(ConstructorRootCharge { root_source_digest: root_source_digest.clone(),
                root_block: block, root_identity: self.entry_identity, root_arguments: arguments, site, vc })
        }).collect()
    }

    fn root_sites(
        &self,
        root: &trust_types::VerifiableFunction,
    ) -> Result<
        Vec<(
            trust_types::BlockId,
            Vec<trust_types::Operand>,
            trust_types::SourceSpan,
            ConstructorSiteRequirement,
        )>,
        String,
    > {
        let mut origins = Vec::new();
        for block in &root.body.blocks {
            match &block.terminator {
                trust_types::Terminator::Call {
                    func,
                    callee_identity,
                    args,
                    span,
                    atomic: None,
                    is_foreign: false,
                    is_unsafe_sig: false,
                    target: Some(_),
                    ..
                } if func == &self.entry.name => {
                    if *callee_identity != Some(self.entry_identity) {
                        return Err(
                            "constructor root call has no exact matching compiler identity".into(),
                        );
                    }
                    for site in &self.sites {
                        origins.push((block.id, args.clone(), span.clone(), site.clone()));
                    }
                }
                trust_types::Terminator::Call { func, callee_identity, .. }
                | trust_types::Terminator::TailCall { func, callee_identity, .. }
                    if func == &self.entry.name
                        || *callee_identity == Some(self.entry_identity) =>
                {
                    return Err(
                        "constructor root call uses an unsupported or aliased call form".into()
                    );
                }
                _ => {}
            }
        }
        Ok(origins)
    }
}

/// Proof-free, closed inventory. The caller must still reconcile this plan
/// against the actual lowered members and every public per-call-site VC before
/// changing import or proof authority. In particular this is not a totality
/// summary: it contains reported requirements only, never an assumed ensures.
pub(super) fn plan_for_member(
    entry: &trust_types::VerifiableFunction,
    members: &[trust_types::VerifiableFunction],
    identities: &BundledMemberSourceIdentityLedger,
    qualifications: &ConstructorQualifications,
) -> Result<ConstructorPlan, String> {
    fn visit(
        member: &trust_types::VerifiableFunction,
        members: &[trust_types::VerifiableFunction],
        identities: &BundledMemberSourceIdentityLedger,
        qualifications: &ConstructorQualifications,
        active: &mut Vec<BundledMemberSourceIdentityKey>,
        work: &mut usize,
        coverage: &mut FxHashSet<BundledMemberSourceIdentityKey>,
    ) -> Result<Vec<ConstructorSiteRequirement>, String> {
        *work += 1;
        if *work > 64 || active.len() >= 6 {
            return Err("constructor closure work/depth limit exceeded".into());
        }
        let key = bundled_member_source_identity_key(member)?;
        if active.contains(&key) {
            return Err("cyclic constructor call closure".into());
        }
        if members
            .iter()
            .filter(|other| other.name == member.name || other.def_path == member.def_path)
            .count()
            != 1
            || member.name != member.def_path
        {
            return Err("constructor member source/display identity is ambiguous".into());
        }
        let retained = members
            .iter()
            .find(|other| other.name == member.name)
            .ok_or("constructor entry is absent from the actual member population")?;
        if bundled_member_source_identity_key(retained)? != key {
            return Err("constructor entry differs from the actual retained member bytes".into());
        }
        let qualification = qualifications
            .get(&key)
            .ok_or("constructor member lacks an exact compiler qualification")?;
        let provenance = identities
            .get(&key)
            .ok_or("constructor member lacks an exact compiler source ledger entry")?;
        if !provenance.def_is_foreign || provenance.identity != Some(qualification.identity) {
            return Err("constructor qualification and compiler source identity disagree".into());
        }
        if !member.contracts.is_empty()
            || !member.postconditions.is_empty()
            || !member.spec.requires.is_empty()
            || !member.spec.ensures.is_empty()
            || !member.spec.invariants.is_empty()
            || !only_exact_intrinsic_integer_bounds(member)
        {
            return Err("constructor safety composition cannot erase member contracts".into());
        }
        let local = trust_ir_bridge::bundled_constructor_local_safety_sites(member)
            .map_err(str::to_string)?;
        let calls =
            trust_ir_bridge::bundled_constructor_call_sites(member).map_err(str::to_string)?;
        validate_member_effect_inventory(member, &local, &qualification.no_drop_blocks)?;
        coverage.insert(key.clone());
        let make_site = |source, requirement| ConstructorSiteRequirement {
            owner_name: key.name.clone(),
            owner_def_path: key.def_path.clone(),
            owner_source_digest: key.source_digest.clone(),
            owner_identity: qualification.identity,
            owner_role: qualification.role,
            source,
            path: Vec::new(),
            requirement,
        };
        let mut sites: Vec<_> = local
            .into_iter()
            .map(|site| {
                let requirement = site.requirement.clone();
                make_site(ConstructorSourceSite::Safety(site), Some(requirement))
            })
            .collect();
        for block in &member.body.blocks {
            if let trust_types::Terminator::Drop { place, span, .. } = &block.terminator {
                sites.push(make_site(
                    ConstructorSourceSite::NoDrop {
                        block: block.id,
                        span: span.clone(),
                        place: place.clone(),
                    },
                    None,
                ));
            }
        }
        active.push(key.clone());
        for call in calls {
            let mut matches = members
                .iter()
                .filter(|child| child.name == call.callee || child.def_path == call.callee);
            let child = matches.next().ok_or("constructor call body is absent")?;
            if matches.next().is_some() {
                return Err("constructor call resolves to multiple bundled bodies".into());
            }
            let child_key = bundled_member_source_identity_key(child)?;
            if identities.get(&child_key).and_then(|source| source.identity) != Some(call.identity)
            {
                return Err("constructor call identity differs from its exact bundled body".into());
            }
            for mut site in
                visit(child, members, identities, qualifications, active, work, coverage)?
            {
                if let Some(requirement) = &site.requirement {
                    site.requirement = Some(
                        trust_ir_bridge::bundled_constructor_rebind_requirement(
                            member,
                            &call,
                            child,
                            requirement,
                        )
                        .map_err(str::to_string)?,
                    );
                }
                site.path.insert(
                    0,
                    ConstructorCallPathEdge {
                        caller_name: key.name.clone(),
                        caller_def_path: key.def_path.clone(),
                        caller_source_digest: key.source_digest.clone(),
                        callee_source_digest: child_key.source_digest.clone(),
                        call: call.clone(),
                    },
                );
                sites.push(site);
                if sites.len() > 128 {
                    return Err("constructor source-site/path inventory limit exceeded".into());
                }
            }
        }
        active.pop();
        Ok(sites)
    }
    let mut coverage = FxHashSet::default();
    let sites =
        visit(entry, members, identities, qualifications, &mut Vec::new(), &mut 0, &mut coverage)?;
    let entry_key = bundled_member_source_identity_key(entry)?;
    let entry_identity = qualifications
        .get(&entry_key)
        .ok_or("constructor entry qualification disappeared")?
        .identity;
    Ok(ConstructorPlan { entry: entry_key, entry_identity, sites, members: coverage })
}

/// Recognize only the extractor's intrinsic integer-parameter type bounds.
/// These are checked against actual local identity, width and signedness;
/// they are never composed into reported safety obligations or assumed as a
/// narrowed authored contract. This lane rejects every additional premise.
fn only_exact_intrinsic_integer_bounds(member: &trust_types::VerifiableFunction) -> bool {
    let mut expected = Vec::new();
    for local in &member.body.locals {
        if local.index == 0 || local.index > member.body.arg_count {
            continue;
        }
        let trust_types::Ty::Int { width, signed } = local.ty else {
            continue;
        };
        if width == 0 || width > 64 {
            continue;
        }
        let Some(name) = local.name.as_deref() else {
            continue;
        };
        let unique =
            member.body.locals.iter().filter(|other| other.name.as_deref() == Some(name)).count()
                == 1;
        let canonical = if unique { name.to_string() } else { format!("_{}", local.index) };
        let (min, max) = if signed {
            (-(1i128 << (width - 1)), (1i128 << (width - 1)) - 1)
        } else {
            (0, (1i128 << width) - 1)
        };
        let variable = || Formula::var(&canonical, trust_types::Sort::Int);
        expected.push(Formula::And(vec![
            Formula::Ge(Box::new(variable()), Box::new(Formula::Int(min))),
            Formula::Le(Box::new(variable()), Box::new(Formula::Int(max))),
        ]));
    }
    member.preconditions == expected
}

/// Optimized setup MIR retains shared-reference declarations whose operations
/// have disappeared. Permit no VALUE behavior for them: even storage markers,
/// a projected/index use, call destination, or an unknown effect counts as a
/// mention and keeps the pointer refusal. The declaration itself is retained.
fn constructor_mentions_local(member: &trust_types::VerifiableFunction, local: usize) -> bool {
    use trust_types::{Operand as O, Rvalue as R, Statement as S, Terminator as T};
    let place_mentions = |place: &trust_types::Place| {
        place.local == local
        || place.projections.iter().any(|projection|
            matches!(projection, trust_types::Projection::Index(index) if *index == local))
    };
    let operand_mentions = |operand: &trust_types::Operand| match operand {
        O::Copy(place) | O::Move(place) => place_mentions(place),
        O::Constant(_) => false,
        _ => true,
    };
    member.body.blocks.iter().any(|block| {
        block.stmts.iter().any(|statement| match statement {
            S::Assign { place, rvalue, .. } => {
                place_mentions(place)
                    || match rvalue {
                        R::Use(value) | R::Cast(value, _) => operand_mentions(value),
                        R::BinaryOp(_, left, right) => {
                            operand_mentions(left) || operand_mentions(right)
                        }
                        R::Aggregate(_, values) => values.iter().any(operand_mentions),
                        _ => true,
                    }
            }
            S::StorageLive(index) | S::StorageDead(index) => *index == local,
            S::Nop | S::Coverage | S::ConstEvalCounter => false,
            _ => true,
        }) || match &block.terminator {
            T::SwitchInt { discr, .. } => operand_mentions(discr),
            T::Assert { cond, .. } => operand_mentions(cond),
            T::Call { args, dest, .. } => place_mentions(dest) || args.iter().any(operand_mentions),
            T::Drop { place, .. } => place_mentions(place),
            T::Goto(_) | T::Return | T::Resume => false,
            _ => true,
        }
    })
}

/// Close the local analyzer's deliberately small safety inventory. This lane
/// admits plain scalar/aggregate MIR operations only. Pointer/enum/unchecked
/// arithmetic/opaque operations need their own faithful obligations first.
fn validate_member_effect_inventory(
    member: &trust_types::VerifiableFunction,
    sites: &[trust_ir_bridge::BundledConstructorSafetySite],
    no_drop_blocks: &[trust_types::BlockId],
) -> Result<(), String> {
    use trust_types::{BinOp as B, Rvalue as R, Statement as S, Terminator as T};
    fn plain_type(ty: &trust_types::Ty, fuel: usize) -> bool {
        if fuel == 0 {
            return false;
        }
        match ty {
            trust_types::Ty::Bool | trust_types::Ty::Unit | trust_types::Ty::Never => true,
            trust_types::Ty::Int { width, .. } => matches!(width, 8 | 16 | 32 | 64 | 128),
            trust_types::Ty::Tuple(fields) => {
                fields.iter().all(|field| plain_type(field, fuel - 1))
            }
            trust_types::Ty::Adt {
                adt_kind: Some(trust_types::AdtKind::Struct),
                fields,
                variants,
                ..
            } => variants.is_empty() && fields.iter().all(|(_, field)| plain_type(field, fuel - 1)),
            _ => false,
        }
    }
    if member.body.locals.iter().any(|local| {
        !plain_type(&local.ty, 8)
            // Trust (1.101): the dead-reference exemption no longer asks the
            // reference's mutability. `SpecRangeSetup::setup`'s optimized MIR
            // now also retains an unmentioned `&mut Range` declaration (the
            // inlined `AsLegacyRange::as_legacy_range_mut` identity accessor's
            // result, whose uses optimized away to a direct field store); a
            // local with no mention at all — the discipline above counts even
            // a storage marker as a mention — carries no value behavior
            // whatever its declared mutability.
            && !(local.index > member.body.arg_count
                && matches!(&local.ty, trust_types::Ty::Ref { inner, .. }
                if plain_type(inner, 8) && !constructor_mentions_local(member, local.index)))
    }) {
        return Err(
            "constructor contains a pointer, enum, opaque, or unsupported local type".into()
        );
    }
    trust_vcgen::validate_function(member)
        .map_err(|error| format!("invalid constructor MIR: {error}"))?;
    let mut covered = Vec::new();
    for site in sites {
        for operation in &site.guarded_operations {
            if covered.contains(operation) {
                return Err(
                    "constructor arithmetic operation is charged by duplicate source sites".into(),
                );
            }
            covered.push(*operation);
        }
    }
    let mut arithmetic = Vec::new();
    let mut drops = Vec::new();
    for block in &member.body.blocks {
        for (index, statement) in block.stmts.iter().enumerate() {
            match statement {
                S::Assign { place, rvalue, .. } => {
                    if place
                        .projections
                        .iter()
                        .any(|projection| !matches!(projection, trust_types::Projection::Field(_)))
                    {
                        return Err(
                            "constructor writes through an unsupported place projection".into()
                        );
                    }
                    match rvalue {
                        R::Use(_)
                        | R::Aggregate(trust_types::AggregateKind::Adt { .. }, _)
                        | R::Aggregate(trust_types::AggregateKind::Tuple, _) => {}
                        R::Cast(_, trust_types::Ty::Int { .. }) => {}
                        R::BinaryOp(B::Div | B::Rem, _, _) => {
                            let Some(local) =
                                member.body.locals.iter().find(|local| local.index == place.local)
                            else {
                                return Err("constructor arithmetic destination has no type".into());
                            };
                            if !place.projections.is_empty()
                                || !matches!(local.ty, trust_types::Ty::Int { signed: false, .. })
                            {
                                return Err("constructor division needs additional signed-overflow or projected-type support".into());
                            }
                            arithmetic.push((block.id, index));
                        }
                        R::BinaryOp(
                            B::Add
                            | B::Sub
                            | B::Mul
                            | B::Eq
                            | B::Ne
                            | B::Lt
                            | B::Le
                            | B::Gt
                            | B::Ge
                            | B::BitAnd
                            | B::BitOr
                            | B::BitXor,
                            _,
                            _,
                        ) => {}
                        _ => {
                            return Err(
                                "constructor contains an unsupported value/unsafe operation".into(),
                            );
                        }
                    }
                }
                S::StorageLive(_)
                | S::StorageDead(_)
                | S::Nop
                | S::Coverage
                | S::ConstEvalCounter => {}
                _ => return Err("constructor contains an unsupported statement effect".into()),
            }
        }
        match &block.terminator {
            T::Goto(_) | T::SwitchInt { .. } | T::Return | T::Resume | T::Assert { .. } => {}
            T::Call { atomic: None, is_foreign: false, is_unsafe_sig: false, .. } => {}
            T::Drop { .. } => drops.push(block.id),
            _ => return Err("constructor contains an unsupported terminator effect".into()),
        }
    }
    arithmetic.sort_by_key(|(block, statement)| (block.0, *statement));
    covered.sort_by_key(|(block, statement)| (block.0, *statement));
    drops.sort_by_key(|block| block.0);
    let mut expected_drops = no_drop_blocks.to_vec();
    expected_drops.sort_by_key(|block| block.0);
    if arithmetic != covered {
        return Err("constructor division/remainder source-site coverage is incomplete".into());
    }
    // Every `Drop` the extraction kept must be one the compiler certified a no-op.
    // Trust (2026-09-29): a SUBSET, no longer an exact match. The extractor now lowers
    // a monomorphic drop whose type `!needs_drop` to a plain edge (the same
    // `Ty::needs_drop` question `no_drop_blocks` is built from), so the extracted body
    // keeps none of these sites, and the exact match refused every step-by constructor
    // (`(0..n).step_by(2).count()`, measured). What the check protects is unchanged:
    // no Drop with real destructor semantics survives into an admitted constructor.
    if drops.iter().any(|block| !expected_drops.contains(block)) {
        return Err("constructor drop sites are not all compiler no-drop facts".into());
    }
    Ok(())
}
