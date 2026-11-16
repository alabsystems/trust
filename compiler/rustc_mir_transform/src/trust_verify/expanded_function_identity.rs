//! Trust: narrowly scoped provenance for one local `macro_rules!` expansion.
//!
//! This identifies the compiler-captured typed input, not ordinary function
//! source. The compiler owns the expansion, complete macro-item and invocation
//! spans. No text parser guesses their extent and no presented proof supplies
//! this record. Other origins remain unavailable.

use trust_types::expanded_function_identity::{
    EXPANDED_FUNCTION_IDENTITY_SCHEMA, ExpandedFunctionIdentity, ExpansionSourceFragment,
    expanded_typed_input_digest,
};

use super::*;

pub(super) fn capture(
    tcx: TyCtxt<'_>,
    owner: LocalDefId,
    function: &trust_types::VerifiableFunction,
    contracts: &trust_types::CompilerContractBundle,
) -> Option<ExpandedFunctionIdentity> {
    let origin = super::expanded_function_origin::capture(tcx, owner)?;
    if origin.function_path != function.def_path {
        return None;
    }
    let identity = ExpandedFunctionIdentity {
        schema: EXPANDED_FUNCTION_IDENTITY_SCHEMA.into(),
        function_path: origin.function_path,
        function_def_path_hash: origin.function_def_path_hash,
        macro_path: origin.macro_path,
        macro_def_path_hash: origin.macro_def_path_hash,
        definition: ExpansionSourceFragment::from_exact_snippet(
            source_span_from_rustc_span(tcx, origin.definition_span),
            &origin.definition_text,
        )?,
        invocation: ExpansionSourceFragment::from_exact_snippet(
            source_span_from_rustc_span(tcx, origin.invocation_span),
            &origin.invocation_text,
        )?,
        typed_input_sha256: expanded_typed_input_digest(function, contracts)?,
    };
    identity.matches_input(function, contracts).then_some(identity)
}
