//! Identity and original-contract binding shared by native verifier adapters.
//! Successful validation establishes correspondence, never proof authority.

use trust_ir::{Module, ProofDigestAlgorithm, ProofObligation};

use crate::{
    ContractKind, ContractPredicate, ObligationKind, TrustContractBundle, TrustObligation,
};

/// Supported original source-contract encodings shared by native adapters.
/// This is a codec discriminator, not evidence that any claim is proved.
pub fn is_supported_raw_source_contract_schema(schema: &str) -> bool {
    matches!(
        schema,
        crate::TRUST_SPEC_PREDICATE_SCHEMA_VERSION
            | trust_types::trust_formula_v1::TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION
            | "trust-wp.pure-expr.v1"
            | "trust-types.Formula@1"
    )
}

/// Syntactic candidate only. A caller must still validate the entire native
/// claim and provenance before using this to classify an encoding gap.
/// Direct typed MC contracts and unknown codecs are not raw source clauses.
pub fn has_raw_source_postcondition_contract(
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
) -> bool {
    if obligation.kind != ObligationKind::Postcondition || obligation.proof_item_id.is_some() {
        return false;
    }
    let Some(id) = obligation.contract_id.as_deref() else {
        return false;
    };
    let mut contracts = bundle.contracts.iter().filter(|contract| contract.contract_id == id);
    let Some(contract) = contracts.next() else {
        return false;
    };
    if contracts.next().is_some() || contract.kind != ContractKind::Ensures {
        return false;
    }
    match &contract.predicate {
        ContractPredicate::CanonicalJson { schema, .. }
        | ContractPredicate::TrustIr { schema, .. } => {
            is_supported_raw_source_contract_schema(schema)
        }
        _ => false,
    }
}

/// A mismatch in the shared native-to-public obligation identity check.
/// This is correspondence only, not a proof or a native admission receipt.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NativePublicIdentityError {
    MissingSource,
    MissingPublicIdentity,
    InvalidExpectedSemanticDigest,
    ObligationIdMismatch { actual: String },
    SemanticDigestMismatch { actual: String },
}

impl std::fmt::Display for NativePublicIdentityError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingSource => f.write_str("native claim has no source identity"),
            Self::MissingPublicIdentity => f.write_str("native claim has no public identity"),
            Self::InvalidExpectedSemanticDigest => {
                f.write_str("expected public semantic digest is not canonical SHA-256")
            }
            Self::ObligationIdMismatch { actual } => write!(
                f,
                "native source.public.obligation_id differs from the public obligation: {actual}"
            ),
            Self::SemanticDigestMismatch { actual } => write!(
                f,
                "native source.public.semantic_digest differs from the canonical public obligation: {actual}"
            ),
        }
    }
}

impl std::error::Error for NativePublicIdentityError {}

fn display_eq_sha256_hex(digest: &impl std::fmt::Display, expected_hex: &str) -> bool {
    use std::fmt::Write;
    struct Matcher<'a> {
        prefix: &'a [u8],
        suffix: &'a [u8],
        matched: bool,
    }
    impl std::fmt::Write for Matcher<'_> {
        fn write_str(&mut self, mut s: &str) -> std::fmt::Result {
            if !self.matched {
                return Err(std::fmt::Error);
            }
            let bytes = s.as_bytes();
            let prefix_take = bytes.len().min(self.prefix.len());
            if bytes[..prefix_take] != self.prefix[..prefix_take] {
                self.matched = false;
                return Err(std::fmt::Error);
            }
            self.prefix = &self.prefix[prefix_take..];
            s = &s[prefix_take..];
            let bytes = s.as_bytes();
            if bytes.len() > self.suffix.len() || bytes != &self.suffix[..bytes.len()] {
                self.matched = false;
                return Err(std::fmt::Error);
            }
            self.suffix = &self.suffix[bytes.len()..];
            Ok(())
        }
    }
    let mut m = Matcher { prefix: b"sha256:", suffix: expected_hex.as_bytes(), matched: true };
    write!(m, "{digest}").is_ok() && m.matched && m.prefix.is_empty() && m.suffix.is_empty()
}

/// Bind a native proof's public identity to the independently computed public
/// obligation digest. The caller supplies the digest from the canonical bundle
/// or its validated digest index. This does not validate a formula, source
/// range, proof certificate, or program, and grants no proof authority.
pub fn validate_native_public_obligation_identity(
    proof: &ProofObligation,
    public_obligation_id: &str,
    expected_semantic_digest_sha256: &str,
) -> Result<(), NativePublicIdentityError> {
    let source = proof.source.as_ref().ok_or(NativePublicIdentityError::MissingSource)?;
    let identity =
        source.public.as_ref().ok_or(NativePublicIdentityError::MissingPublicIdentity)?;
    if identity.obligation_id != public_obligation_id {
        return Err(NativePublicIdentityError::ObligationIdMismatch {
            actual: identity.obligation_id.clone(),
        });
    }
    if !trust_types::digest::is_stable_sha256_hex(expected_semantic_digest_sha256) {
        return Err(NativePublicIdentityError::InvalidExpectedSemanticDigest);
    }
    if identity.semantic_digest.algorithm != ProofDigestAlgorithm::Sha256
        || identity.semantic_digest.is_zero()
        || !display_eq_sha256_hex(&identity.semantic_digest, expected_semantic_digest_sha256)
    {
        return Err(NativePublicIdentityError::SemanticDigestMismatch {
            actual: identity.semantic_digest.to_string(),
        });
    }
    Ok(())
}

/// Match the original public program constraints without running a prover.
/// Compiler-origin contexts are covered by the public semantic digest and
/// require both program carriers. Context-less mathematical callers retain
/// their existing unbound behavior when neither carrier is supplied.
/// Request configuration and artifact fingerprints remain separate strategy
/// transport identities; this check grants no source or proof authority.
pub fn validate_native_public_module_binding(
    module: &Module,
    proof: &ProofObligation,
    public: &TrustObligation,
) -> Result<(), String> {
    const MODULE_KEY: &str = "trust.trust_ir.native.trust_ir_module_digest";
    const UNIT_KEY: &str = "trust.trust_ir.native.proof_unit.v1";
    const UNIT_SCHEMA: &str = "trust.trust_ir.native-proof-unit.v1";
    let unique = |key: &str| -> Result<Option<&crate::MetadataEntry>, String> {
        let mut entries = public.metadata.iter().filter(|entry| entry.key == key);
        let first = entries.next();
        if entries.next().is_some() {
            return Err(format!("native public program binding has duplicate `{key}` records"));
        }
        Ok(first)
    };
    let compiler_owned = if let Some(entry) = unique(crate::OBLIGATION_CONTEXT_METADATA_KEY)? {
        // Reuse the original typed context decoder, after the shared ingress
        // has rejected duplicate keys at every level of its raw JSON.
        trust_types::trust_formula_v1::parse_unique_proof_json_payload(&entry.value)
            .map_err(|error| format!("invalid native public obligation context: {error}"))?;
        let context = crate::ObligationContext::from_metadata_entry(entry)
            .map_err(|error| format!("invalid native public obligation context: {error}"))?
            .ok_or("missing native public obligation context")?;
        if !context.has_current_schema() {
            return Err("unsupported native public obligation context schema".into());
        }
        context.producer == crate::ObligationProducer::CompilerMirExtract
    } else {
        false
    };
    let module_entry = unique(MODULE_KEY)?;
    let unit_entry = unique(UNIT_KEY)?;
    if compiler_owned && (module_entry.is_none() || unit_entry.is_none()) {
        return Err(
            "compiler-origin native claim requires both original public program bindings".into()
        );
    }
    if module_entry.is_none() && unit_entry.is_none() {
        return Ok(());
    }
    let actual = module.stable_digest();
    let matches_module = |expected: &str| {
        trust_types::digest::is_stable_sha256_hex(expected)
            && display_eq_sha256_hex(&actual, expected)
    };
    if module_entry.is_some_and(|entry| !matches_module(&entry.value)) {
        return Err("native TrustIr module differs from the original public module digest".into());
    }
    if let Some(entry) = unit_entry {
        // This reads only the original program/obligation constraint. It does
        // not decode another engine's request or reconstruct a proof question.
        let unit = trust_types::trust_formula_v1::parse_unique_proof_json_payload(&entry.value)
            .map_err(|error| format!("invalid native public proof-unit binding: {error}"))?;
        if unit.get("schema_version").and_then(serde_json::Value::as_str) != Some(UNIT_SCHEMA)
            || unit.get("public_obligation_id").and_then(serde_json::Value::as_str)
                != Some(public.obligation_id.as_str())
            || unit.get("proof_obligation_id").and_then(serde_json::Value::as_u64)
                != Some(u64::from(proof.id.index()))
            || !unit.get("trust_ir_module_digest").is_some_and(|digest| {
                digest.get("algorithm").and_then(serde_json::Value::as_str) == Some("sha256")
                    && digest
                        .get("value")
                        .and_then(serde_json::Value::as_str)
                        .is_some_and(|value| matches_module(value))
            })
        {
            return Err("native TrustIr module/obligation differs from the original public proof-unit binding".into());
        }
    }
    Ok(())
}

/// Reconcile a raw native postcondition with the complete canonical public claim,
/// its original typed contract, and its exact parameter/result binding map.
pub fn validate_native_public_contract_claim(
    module: &Module,
    proof: &ProofObligation,
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
) -> Result<(), String> {
    validate_raw_contract_claim(module, proof, bundle, obligation, false)
}

/// Bind an original definition-site entry clause. This does not make the
/// clause a premise: only a sealed public question may expose its entry domain.
pub fn validate_native_public_entry_contract_claim(
    module: &Module,
    proof: &ProofObligation,
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
) -> Result<(), String> {
    if proof.kind != trust_ir::ObligationKind::Precondition || proof.site.is_some() {
        return Err("entry clause must be an original definition-site precondition".into());
    }
    validate_raw_contract_claim(module, proof, bundle, obligation, true)?;
    let function = proof
        .function
        .and_then(|id| module.function_by_id(id))
        .ok_or("entry clause has no original owning function")?;
    let signature = module.func_type(function.ty).ok_or("entry function has no signature")?;
    for (_, binding) in &proof.formula.as_ref().ok_or("entry clause has no formula")?.bindings {
        let trust_ir::proof::ClausePlace::Param { index } = binding.place else {
            return Err("entry clause must bind original parameters".into());
        };
        if usize::try_from(index).ok().and_then(|index| signature.params.get(index)).is_none() {
            return Err("entry clause parameter is absent from the original signature".into());
        }
    }
    Ok(())
}

fn validate_raw_contract_claim(
    module: &Module,
    proof: &ProofObligation,
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
    entry: bool,
) -> Result<(), String> {
    validate_native_public_module_binding(module, proof, obligation)?;
    validate_native_public_source_projection(module, proof, obligation)?;
    let expected = if entry { ObligationKind::Precondition } else { ObligationKind::Postcondition };
    if obligation.kind != expected || obligation.proof_item_id.is_some() {
        return Err(
            "native raw contract claim must be a postcondition of its original contract".into()
        );
    }
    let digest = bundle.canonical_obligation_semantic_digest_sha256(obligation)?;
    validate_native_public_obligation_identity(proof, &obligation.obligation_id, &digest)
        .map_err(|error| error.to_string())?;
    let formula = proof.formula.as_ref().ok_or("native raw claim has no typed formula")?;
    let contract = obligation
        .contract_id
        .as_ref()
        .and_then(|id| bundle.contracts.iter().find(|contract| &contract.contract_id == id))
        .ok_or("native raw claim requires the original typed public postcondition")?;
    if if entry {
        !matches!(contract.kind, ContractKind::Requires | ContractKind::Assumes)
    } else {
        contract.kind != ContractKind::Ensures
    } {
        return Err("native raw postcondition is not bound to an Ensures contract".into());
    }
    let (schema, value) = match &contract.predicate {
        ContractPredicate::CanonicalJson { schema, value }
        | ContractPredicate::TrustIr { schema, value } => (schema, value),
        _ => return Err("native raw claim requires a canonical typed public postcondition".into()),
    };
    if !is_supported_raw_source_contract_schema(schema) {
        return Err("native raw claim uses an unsupported source-contract codec".into());
    }
    let mut typed_scalar_bindings = None;
    let same_formula = if schema == crate::TRUST_SPEC_PREDICATE_SCHEMA_VERSION {
        let predicate = crate::TrustSpecPredicate::from_contract_predicate(&contract.predicate)
            .map_err(|error| format!("invalid typed public postcondition: {error}"))?
            .ok_or("missing typed public postcondition")?;
        let expected =
            crate::trust_spec_native_formula::trust_spec_predicate_to_trust_formula_payload(
                &predicate,
            )?;
        typed_scalar_bindings = Some(original_typed_scalar_bindings(&predicate)?);
        // Compare the same strict encoding under either serde map feature.
        // Raw proof input must reject duplicate keys before canonicalization;
        // normalization grants correspondence only and never changes input.
        formula.schema == trust_types::trust_formula_v1::TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION
            && expected
                == trust_types::trust_formula_v1::parse_arithmetic_free_trust_formula_v1_payload(
                    &formula.payload,
                )
                .map_err(|error| format!("invalid native raw postcondition: {error}"))?
    } else if let Some(text) = value.as_str() {
        schema == &formula.schema && text == formula.payload
    } else {
        schema == &formula.schema && {
            // A typed JSON public predicate still corresponds to raw proof
            // text. Use the same unique-key ingress as the typed-contract
            // path; Value decoding alone silently drops duplicate keys.
            let native =
                trust_types::trust_formula_v1::parse_unique_proof_json_payload(&formula.payload)
                    .map_err(|error| format!("invalid native raw postcondition: {error}"))?;
            &native == value
        }
    };
    if !same_formula {
        return Err("native formula differs from the original public postcondition".into());
    }
    if formula.smtlib.is_some() || formula.sort.is_some() {
        return Err("raw source postcondition carries body-VC rendering metadata".into());
    }
    let mut maps = contract
        .metadata
        .iter()
        .filter(|entry| entry.key == crate::TRUST_IR_CLAUSE_BINDINGS_METADATA_KEY);
    let map = maps.next().ok_or("native raw public contract has no typed binding map")?;
    if maps.next().is_some() {
        return Err("native raw public contract has ambiguous typed binding maps".into());
    }
    let bindings: Vec<(String, trust_ir::proof::ClauseBinding)> = serde_json::from_str(&map.value)
        .map_err(|_| "native raw public contract binding map is invalid")?;
    let mut names =
        rustc_hash::FxHashSet::with_capacity_and_hasher(bindings.len(), Default::default());
    if bindings.iter().any(|(name, _)| !names.insert(name.as_str())) {
        return Err("native raw public contract has duplicate binding names".into());
    }
    if bindings != formula.bindings {
        return Err("native parameter/result bindings differ from the public contract".into());
    }
    if entry
        && bindings.iter().any(|(_, binding)| {
            !matches!(binding.place, trust_ir::proof::ClausePlace::Param { .. })
        })
    {
        return Err("entry clause bindings must denote original function parameters".into());
    }
    if let Some(originals) = typed_scalar_bindings {
        let by_name: rustc_hash::FxHashMap<_, _> =
            bindings.iter().map(|(name, binding)| (name.as_str(), binding)).collect();
        for original in originals {
            if entry && original.is_result_placeholder {
                return Err("entry clause cannot refer to the returned result".into());
            }
            let carrier = by_name.get(original.name.as_str()).ok_or_else(|| {
                format!("native typed public contract has no binding for `{}`", original.name)
            })?;
            // The public scalar Int is encoded by either a mathematical Int
            // or an explicit machine-integer carrier. Preserve that ORIGINAL
            // width/place in the exact map above; the owning native validator
            // and body binder must still authenticate it against the program.
            // In particular Bool is never an integer, even a one-bit carrier.
            let same_domain = matches!(
                (original.sort, &carrier.sort),
                (crate::TrustSpecSort::Bool, trust_ir::proof::ClauseSort::Bool)
                    | (crate::TrustSpecSort::Int, trust_ir::proof::ClauseSort::Int)
                    | (crate::TrustSpecSort::Int, trust_ir::proof::ClauseSort::BitVec(_))
            );
            if !same_domain {
                return Err(format!(
                    "native binding `{}` scalar domain {:?} differs from original typed public sort {:?}",
                    original.name, carrier.sort, original.sort,
                ));
            }
            if original.is_result_placeholder
                && carrier.place != (trust_ir::proof::ClausePlace::ResultSlot { index: 0 })
            {
                return Err(format!(
                    "native binding for the original typed Result placeholder must denote ResultSlot(0), not {:?}",
                    carrier.place,
                ));
            }
        }
    }
    Ok(())
}

/// Original typed declaration facts, never inferred from a binding's spelling.
struct OriginalTypedScalarBinding {
    name: String,
    sort: crate::TrustSpecSort,
    is_result_placeholder: bool,
}

/// Read the same supported typed tree already checked by the strict converter.
/// Its result sort is globally consistent there; names and scalar domains here
/// bind the original public declaration to the carried parameter/result map.
fn original_typed_scalar_bindings(
    predicate: &crate::TrustSpecPredicate,
) -> Result<Vec<OriginalTypedScalarBinding>, String> {
    use crate::TrustSpecExprKind;
    let mut bindings: Vec<_> = predicate
        .variables
        .iter()
        .map(|variable| OriginalTypedScalarBinding {
            name: variable.name.clone(),
            sort: variable.sort,
            is_result_placeholder: false,
        })
        .collect();
    let mut pending = vec![&predicate.root];
    while let Some(expr) = pending.pop() {
        match &expr.kind {
            TrustSpecExprKind::Result => {
                bindings.push(OriginalTypedScalarBinding {
                    name: "result".into(),
                    sort: expr.sort,
                    is_result_placeholder: true,
                });
                break;
            }
            TrustSpecExprKind::Unary { expr, .. } | TrustSpecExprKind::Old { expr } => {
                pending.push(expr);
            }
            TrustSpecExprKind::Binary { lhs, rhs, .. } => {
                pending.push(rhs);
                pending.push(lhs);
            }
            TrustSpecExprKind::BoolLiteral { .. }
            | TrustSpecExprKind::IntLiteral { .. }
            | TrustSpecExprKind::Variable { .. } => {}
            _ => return Err("unsupported original typed native scalar claim".into()),
        }
    }
    Ok(bindings)
}

/// Require the native source identity and complete range to be the canonical
/// projection of the public obligation. This checks correspondence only; it
/// grants no authority to the producer, engine, or proof.
pub fn validate_native_public_source_projection(
    module: &Module,
    proof: &ProofObligation,
    public: &TrustObligation,
) -> Result<(), String> {
    let embedded_source = proof.source.as_ref().ok_or_else(|| {
        format!(
            "native TrustIr proof obligation {} is missing its embedded source identity",
            proof.id.index()
        )
    })?;
    let expected_source_id = public
        .contract_id
        .as_deref()
        .or(public.proof_item_id.as_deref())
        .unwrap_or(&public.obligation_id);
    if embedded_source.source_id != expected_source_id
        || embedded_source.assertion_id.strip_prefix("trust-assertion:") != Some(expected_source_id)
    {
        let expected_assertion_id = format!("trust-assertion:{expected_source_id}");
        return Err(format!(
            "native TrustIr proof obligation {} source/assertion identity {:?}/{:?} does not match canonical public projection {:?}/{:?}",
            proof.id.index(),
            embedded_source.source_id,
            embedded_source.assertion_id,
            expected_source_id,
            expected_assertion_id
        ));
    }
    match (public.source.file.as_deref(), embedded_source.range) {
        (None, None) => Ok(()),
        (None, Some(range)) => Err(format!(
            "native TrustIr proof obligation {} embeds source range {range:?}, but public source has no file",
            proof.id.index()
        )),
        (Some(file), None) => Err(format!(
            "native TrustIr proof obligation {} omits its source range for public file {file:?}",
            proof.id.index()
        )),
        (Some(file), Some(range)) => {
            let embedded_file = module.file_name(range.file).ok_or_else(|| {
                format!(
                    "native TrustIr proof obligation {} source range references missing file index {}",
                    proof.id.index(),
                    range.file
                )
            })?;
            let start_line = public.source.line.unwrap_or_default();
            let start_col = public.source.column.unwrap_or_default();
            let end_line = public.source.end_line.unwrap_or(start_line);
            let end_col = public.source.end_column.unwrap_or(start_col);
            if embedded_file != file
                || range.start_line != start_line
                || range.start_col != start_col
                || range.end_line != end_line
                || range.end_col != end_col
            {
                return Err(format!(
                    "native TrustIr proof obligation {} embedded source range {embedded_file:?}:{}:{}-{}:{} does not exactly match public source {file:?}:{start_line}:{start_col}-{end_line}:{end_col}",
                    proof.id.index(),
                    range.start_line,
                    range.start_col,
                    range.end_line,
                    range.end_col
                ));
            }
            Ok(())
        }
    }
}
