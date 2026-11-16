//! Trust (C1, 2026-11-06): the ONE production issuer of trust-mc's live
//! `SourceReferenceFacts` (`docs/DECISION_QUEUE.md`, 2026-11-06, "source
//! reference facts reach the native solve").
//!
//! trust-mc's source-consumption gate admits a load through an erased reference
//! only with these facts, and only from "the audited live source-lowering seam"
//! (trust-mc `source_reference.rs`, the constructor's semantic-TCB contract).
//! This is that seam. Its inputs are:
//!
//! * the bridge's side table (`trust_ir_bridge::LoweredSourceReferenceSites`),
//!   recorded while the SOURCE type was visible, only for functions the compiler
//!   attested borrow-provenance-clean, only for `&bool`/`&int` references or
//!   (2026-11-07) finite products of them and valtree reference-constant
//!   values, and
//!   kept paired with the exact module the bundle was built from
//!   (`build_native_trust_ir_bundle_from_verifiable_functions`), with conjunct
//!   (3)'s withdrawals applied;
//! * the FINAL native bundle and the authority minted for it.
//!
//! Every claim is reconciled against the final module by value identity
//! (`LoweredSourceReferenceSites::reconcile`): a missing, ambiguous or rewritten
//! site is dropped, never repaired. If the constructor still refuses the
//! survivors, the answer is `None`, today's fail-closed behaviour; no retry with
//! fewer claims is attempted (a retry chosen by error text would let the error
//! decide which claims to trust).
//!
//! Trust (2026-11-07): the constructor is now the value-fact one
//! (`from_live_source_lowering_with_values`), still called exactly once, here.
//! Its value records are the bridge's reference VALUE sites: the stamped
//! `Undef(Ptr)` of the promoted shared borrow of a stateless ZST, a
//! valtree-recovered fieldless struct (`&UnitStruct`; the 2026-11-07 review
//! narrowed the first cut, which also took `&Enum::UnitVariant` and
//! `&Newtype(N)`) or, since 2026-11-10 (EMPTY-CLOSURE-REF-VALUE-1), an
//! upvar-free closure (`&|x| x / 2`, the extractor's `ConstValue::EmptyClosureRef`,
//! the carrier trust-mc's value-fact contract names). Each claims only that the
//! erased pointer bits are initialized; no address, pointee, memory or
//! `ValidBorrow` fact follows from it (`docs/TCB.md`, "Source reference facts";
//! `docs/DECISION_QUEUE.md`, 2026-11-07 and 2026-11-10).
//!
//! What is claimed, and why it is true, is semantic TCB (`docs/TCB.md`, "Source
//! reference facts").

/// Reconcile `sites` against `native_bundle`'s final module and bind the
/// survivors to the live bundle and its authority. `None` when the authority does
/// not authorize this bundle, when no claim survives, or when trust-mc's
/// constructor refuses the claims.
pub(super) fn source_reference_facts_for_live_native_bundle<'a>(
    native_bundle: &'a trust_ir_bridge::NativeVerificationBundle,
    authority: &'a trust_ir_bridge::SourceGenerationAuthority,
    sites: &trust_ir_bridge::LoweredSourceReferenceSites,
) -> Option<trust_router::NativeSourceReferenceFacts<'a>> {
    if !authority.authorizes_bundle(native_bundle) {
        return None;
    }
    let reconciled = sites.reconcile(&native_bundle.module);
    if std::env::var_os("TRUST_SOURCE_REFERENCE_TRACE").is_some() {
        // DIAGNOSTIC ONLY: what the seam saw; changes no verdict.
        let mut claimed: Vec<&str> = sites.claimed_def_paths().collect();
        claimed.sort_unstable();
        eprintln!(
            "[SOURCE_REFERENCE] claimed={} parameters={} loads={} values={} withdrawn={} functions={:?}",
            sites.claim_count(),
            reconciled.parameters.len(),
            reconciled.loads.len(),
            reconciled.values.len(),
            reconciled.withdrawn,
            claimed,
        );
    }
    bind_reconciled_source_reference_facts(native_bundle, authority, reconciled)
}

/// The single call of trust-mc's constructor. `None` for an empty claim set, so a
/// bundle with nothing claimed keeps the exact authority-only dispatch it had.
pub(super) fn bind_reconciled_source_reference_facts<'a>(
    native_bundle: &'a trust_ir_bridge::NativeVerificationBundle,
    authority: &'a trust_ir_bridge::SourceGenerationAuthority,
    reconciled: trust_ir_bridge::ReconciledSourceReferenceSites,
) -> Option<trust_router::NativeSourceReferenceFacts<'a>> {
    if reconciled.is_empty() {
        return None;
    }
    let parameters = reconciled
        .parameters
        .into_iter()
        .map(|parameter| trust_router::NativeSourceReferenceParameterFact {
            function: parameter.function,
            parameter_index: parameter.parameter_index,
            value: parameter.value,
            pointee: parameter.pointee,
        })
        .collect();
    let loads = reconciled
        .loads
        .into_iter()
        .map(|load| trust_router::NativeSourceReferenceLoadFact {
            function: load.function,
            block: load.block,
            instruction_index: load.instruction_index,
            result: load.result,
            pointer: load.pointer,
            pointee: load.pointee,
        })
        .collect();
    let values = reconciled
        .values
        .into_iter()
        .map(|value| trust_router::NativeSourceReferenceValueFact {
            function: value.function,
            block: value.block,
            instruction_index: value.instruction_index,
            result: value.result,
        })
        .collect();
    match trust_router::NativeSourceReferenceFacts::from_live_source_lowering_with_values(
        native_bundle,
        authority,
        parameters,
        loads,
        values,
    ) {
        Ok(facts) => Some(facts),
        Err(error) => {
            if std::env::var_os("TRUST_SOURCE_REFERENCE_TRACE").is_some() {
                eprintln!("[SOURCE_REFERENCE] constructor refused the claims: {error}");
            }
            None
        }
    }
}
