//! One original public/native question, including its declared entry domain.
//!
//! This is a correspondence boundary, not a proof or a source-generation
//! authority. It does not interpret a program or supply an engine algorithm.

use trust_ir::{FuncId, NativeVerificationBundle, ProofId, ProofObligation, ValidatedNativeBundle};

use crate::native_contract_claim::{
    validate_native_public_contract_claim, validate_native_public_entry_contract_claim,
};
use crate::{
    ContractKind, ObligationContext, ObligationKind, ObligationOrigin, TrustContractBundle,
    TrustObligation,
};

/// A derivation choice over the same original question, never proof authority.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum NativePublicProofScope {
    /// Establish the postcondition for all supported inputs, without premises.
    Unconditional,
    /// Establish it under the exact original declared entry domain.
    DeclaredEntry,
}

/// An entry predicate matched to both original carriers. Private fields prevent
/// engine-local metadata or a function summary from manufacturing this fact.
#[derive(Debug)]
pub struct NativeEntryPrecondition<'a> {
    proof: &'a ProofObligation,
    public: &'a TrustObligation,
    function: FuncId,
}

impl<'a> NativeEntryPrecondition<'a> {
    pub fn proof(&self) -> &'a ProofObligation {
        self.proof
    }

    pub fn public_obligation(&self) -> &'a TrustObligation {
        self.public
    }

    pub fn function(&self) -> FuncId {
        self.function
    }
}

/// Immutably borrowed, admitted original postcondition and complete declared
/// entry inventory. This object cannot be decoded from producer JSON or built
/// from a digest. A changed public clause or native packet requires a new one.
///
/// Entry clauses are premises only at entry to their own function. At a local
/// call they are obligations of the caller, and arbitrary body/callee Assume
/// instructions and assertions remain owed. Engines must implement those rules;
/// construction alone establishes no verdict, definedness or proof grade.
#[derive(Debug)]
pub struct NativePublicQuestion<'a> {
    public: &'a TrustContractBundle,
    native: &'a NativeVerificationBundle,
    obligation: &'a TrustObligation,
    proof: &'a ProofObligation,
    function: FuncId,
    entries: Vec<NativeEntryPrecondition<'a>>,
    digest: String,
    scope: NativePublicProofScope,
}

impl<'a> NativePublicQuestion<'a> {
    pub fn new(
        public: &'a TrustContractBundle,
        native: &ValidatedNativeBundle<'a>,
        obligation_id: &str,
    ) -> Result<Self, String> {
        Self::for_derivation(public, native, obligation_id, NativePublicProofScope::DeclaredEntry)
    }

    /// Both scopes bind the identical original question. An unconditional
    /// derivation consumes no premise, including an unsupported declaration.
    pub fn for_derivation(
        public: &'a TrustContractBundle,
        native: &ValidatedNativeBundle<'a>,
        obligation_id: &str,
        scope: NativePublicProofScope,
    ) -> Result<Self, String> {
        public.validate()?;
        let native = native.bundle();
        let obligation = public
            .obligations
            .iter()
            .find(|obligation| obligation.obligation_id == obligation_id)
            .ok_or("public question has no selected obligation")?;
        let proof = original_proof(native, obligation_id)?;
        if proof.kind != trust_ir::ObligationKind::Postcondition || proof.site.is_some() {
            return Err("public body question requires an original function postcondition".into());
        }
        let function = proof.function.ok_or("public question has no original function")?;
        if native.module.function_by_id(function).is_none() {
            return Err("public question function is absent from the original module".into());
        }
        validate_native_public_contract_claim(&native.module, proof, public, obligation)?;
        let post_context = if obligation
            .metadata
            .iter()
            .any(|entry| entry.key == crate::OBLIGATION_CONTEXT_METADATA_KEY)
        {
            let context = function_context(obligation, ContractKind::Ensures)?;
            validate_selected_context(public, native, function, &context)?;
            Some(context)
        } else {
            None
        };

        // Scope is deliberately separate: a stronger unconditional proof and
        // a conditional derivation answer the same original public question.
        // Bind the complete public input even where no entry codec is usable;
        // no declaration may disappear from identity because an engine cannot
        // interpret it. This may invalidate a cache on an unrelated catalog
        // change, but never turns that catalog entry into a premise.
        let digest = question_digest(public, native, obligation, proof, function)?;
        if scope == NativePublicProofScope::Unconditional {
            return Ok(Self {
                public,
                native,
                obligation,
                proof,
                function,
                entries: Vec::new(),
                digest,
                scope,
            });
        }

        let mut entries = Vec::new();
        // Inventory the original unit, including callees. A whole-crate public
        // catalog may also contain declarations outside this native closure.
        for contract in &public.contracts {
            if !matches!(contract.kind, ContractKind::Requires | ContractKind::Assumes) {
                continue;
            }
            let mut definitions = Vec::new();
            let mut outside = false;
            let mut inside = false;
            for candidate in &public.obligations {
                if candidate.contract_id.as_deref() != Some(contract.contract_id.as_str()) {
                    continue;
                }
                if candidate.kind != ObligationKind::Precondition {
                    return Err(
                        "entry contract is referenced by a non-precondition obligation".into()
                    );
                }
                let original = match original_proof(native, &candidate.obligation_id) {
                    Ok(original) => original,
                    Err(error) => {
                        let context = function_context(candidate, contract.kind)?;
                        if post_context.as_ref() != Some(&context)
                            && !native
                                .module
                                .functions
                                .iter()
                                .any(|function| matches_function(public, function, &context))
                        {
                            if native.module.functions.iter().any(|candidate| {
                                (candidate.id != function || post_context.is_none())
                                    && !candidate
                                        .display_path
                                        .as_deref()
                                        .unwrap_or(&candidate.name)
                                        .contains("::")
                            }) {
                                return Err("an unidentified native function prevents excluding an unmatched entry declaration".into());
                            }
                            outside = true;
                            continue;
                        }
                        return Err(error);
                    }
                };
                inside = true;
                // A call-site precondition is owed at that call, never a new
                // declaration of the caller's entry domain.
                if original.site.is_some() {
                    continue;
                }
                validate_native_public_entry_contract_claim(
                    &native.module,
                    original,
                    public,
                    candidate,
                )?;
                let owner = original.function.ok_or("entry declaration has no owning function")?;
                if owner == function {
                    if post_context.as_ref() != Some(&function_context(candidate, contract.kind)?) {
                        return Err(
                            "entry and postcondition must name the same original public function"
                                .into(),
                        );
                    }
                } else {
                    validate_function_context(public, native, original, candidate, contract.kind)?;
                }
                definitions.push(NativeEntryPrecondition {
                    proof: original,
                    public: candidate,
                    function: owner,
                });
            }
            if definitions.is_empty() && outside && !inside {
                continue;
            }
            let mut owners = rustc_hash::FxHashSet::default();
            if definitions.is_empty()
                || definitions.iter().any(|entry| !owners.insert(entry.function))
            {
                return Err(format!(
                    "entry contract `{}` needs one exact original definition per instance, found {}",
                    contract.contract_id,
                    definitions.len(),
                ));
            }
            entries.extend(definitions);
        }
        // A native precondition absent from the public declaration cannot
        // silently become a premise, nor can removing a declaration hide it.
        for original in &native.module.proof_obligations {
            if original.kind == trust_ir::ObligationKind::Precondition
                && original.site.is_none()
                && !entries.iter().any(|entry| entry.proof.id == original.id)
            {
                return Err("native entry precondition has no exact public declaration".into());
            }
        }
        if !entries.is_empty() && post_context.is_none() {
            return Err(
                "declared entry domain requires the original selected function context".into()
            );
        }
        entries.sort_by(|left, right| {
            (left.function.index(), left.public.obligation_id.as_str())
                .cmp(&(right.function.index(), right.public.obligation_id.as_str()))
        });

        Ok(Self { public, native, obligation, proof, function, entries, digest, scope })
    }

    pub fn public_bundle(&self) -> &'a TrustContractBundle {
        self.public
    }

    pub fn native_bundle(&self) -> &'a NativeVerificationBundle {
        self.native
    }

    pub fn public_obligation(&self) -> &'a TrustObligation {
        self.obligation
    }

    pub fn proof(&self) -> &'a ProofObligation {
        self.proof
    }

    pub fn function(&self) -> FuncId {
        self.function
    }

    /// The current complete question identity, not the old Ensures-only digest.
    pub fn digest_sha256(&self) -> &str {
        &self.digest
    }

    pub fn proof_scope(&self) -> NativePublicProofScope {
        self.scope
    }

    pub fn entry_preconditions(
        &self,
        function: FuncId,
    ) -> impl Iterator<Item = &NativeEntryPrecondition<'a>> {
        self.entries.iter().filter(move |entry| entry.function == function)
    }

    /// Whether this derivation consumes any admitted entry premises. A
    /// premise-free scope can still bind public Requires in question identity.
    pub fn has_entry_preconditions(&self) -> bool {
        !self.entries.is_empty()
    }

    pub fn proof_id(&self) -> ProofId {
        self.proof.id
    }
}

fn question_digest(
    public: &TrustContractBundle,
    native: &NativeVerificationBundle,
    obligation: &TrustObligation,
    proof: &ProofObligation,
    function: FuncId,
) -> Result<String, String> {
    // Reuse the existing canonical public-semantic owners. Strategy transport
    // annotations are independently checked by engines and are not premises.
    let mut contracts = std::collections::BTreeMap::new();
    for contract in &public.contracts {
        if matches!(contract.kind, ContractKind::Requires | ContractKind::Assumes) {
            contracts.insert(
                contract.contract_id.as_str(),
                TrustContractBundle::canonical_contract_json_value(contract)?,
            );
        }
    }
    let mut declarations = std::collections::BTreeMap::new();
    for candidate in &public.obligations {
        if candidate.contract_id.as_deref().is_some_and(|id| contracts.contains_key(id)) {
            declarations.insert(
                candidate.obligation_id.as_str(),
                candidate.canonical_semantic_digest_sha256_unchecked()?,
            );
        }
    }
    trust_types::digest::canonical_json_sha256(&(
        "trust.native-public-question.v1",
        native.stable_digest().to_string(),
        public.canonical_obligation_semantic_digest_sha256(obligation)?,
        function.index(),
        proof.id.index(),
        contracts,
        declarations,
    ))
    .map_err(|error| format!("cannot encode native public question identity: {error}"))
}

fn original_proof<'a>(
    native: &'a NativeVerificationBundle,
    public_id: &str,
) -> Result<&'a ProofObligation, String> {
    let mut matches = native.module.proof_obligations.iter().filter(|proof| {
        proof
            .source
            .as_ref()
            .and_then(|source| source.public.as_ref())
            .is_some_and(|identity| identity.obligation_id == public_id)
    });
    let original = matches.next().ok_or("public clause has no original native proof obligation")?;
    if matches.next().is_some() {
        return Err("public clause has ambiguous original native obligations".into());
    }
    Ok(original)
}

fn validate_function_context(
    bundle: &TrustContractBundle,
    native: &NativeVerificationBundle,
    proof: &ProofObligation,
    public: &TrustObligation,
    kind: ContractKind,
) -> Result<(), String> {
    let context = function_context(public, kind)?;
    let function = proof
        .function
        .and_then(|id| native.module.function_by_id(id))
        .ok_or("entry context has no original native function")?;
    if !matches_function(bundle, function, &context) {
        return Err("entry context differs from the original native function".into());
    }
    Ok(())
}

fn function_context(
    public: &TrustObligation,
    kind: ContractKind,
) -> Result<crate::FunctionContext, String> {
    let mut contexts =
        public.metadata.iter().filter(|entry| entry.key == crate::OBLIGATION_CONTEXT_METADATA_KEY);
    let entry = contexts
        .next()
        .ok_or("declared entry domain requires the original public function context")?;
    if contexts.next().is_some() {
        return Err("declared entry domain has ambiguous public function contexts".into());
    }
    trust_types::trust_formula_v1::parse_unique_proof_json_payload(&entry.value)
        .map_err(|error| format!("invalid entry function context: {error}"))?;
    let context = ObligationContext::from_metadata_entry(entry)
        .map_err(|error| format!("invalid entry function context: {error}"))?
        .ok_or("missing entry function context")?;
    if !context.has_current_schema() {
        return Err("unsupported entry function context schema".into());
    }
    let function = context.function.ok_or("entry context has no public function")?;
    match context.origin {
        ObligationOrigin::Contract { contract_id, contract_kind, .. }
            if Some(contract_id.as_str()) == public.contract_id.as_deref()
                && contract_kind == kind =>
        {
            Ok(function)
        }
        _ => Err("entry context is not the original declared contract role".into()),
    }
}

fn matches_function(
    public: &TrustContractBundle,
    function: &trust_ir::Function,
    context: &crate::FunctionContext,
) -> bool {
    if context.crate_name.is_empty() || context.path.is_empty() {
        return false;
    }
    let subject_crate = match &public.subject {
        crate::BundleSubject::Function { crate_name, .. } => Some(crate_name.as_str()),
        crate::BundleSubject::Crate { name } => Some(name.as_str()),
        _ => None,
    };
    let identity = function.display_path.as_deref().unwrap_or(&function.name);
    if identity.contains("::") {
        // This checks the proof's known FuncId; it never selects a function
        // by display path. Distinct monomorphizations can share that path.
        return context.path == identity
            && identity.split("::").next() == Some(context.crate_name.as_str());
    }
    subject_crate == Some(context.crate_name.as_str()) && context.path == identity
}

fn validate_selected_context(
    public: &TrustContractBundle,
    native: &NativeVerificationBundle,
    function: FuncId,
    context: &crate::FunctionContext,
) -> Result<(), String> {
    if let crate::BundleSubject::Function { crate_name, path } = &public.subject {
        if context.crate_name != *crate_name || context.path != *path {
            return Err(
                "selected postcondition context differs from the original public subject".into()
            );
        }
    }
    let original =
        native.module.function_by_id(function).ok_or("selected question function is absent")?;
    let identity = original.display_path.as_deref().unwrap_or(&original.name);
    let exact = matches_function(public, original, context);
    // Historical per-function compiler units retain the exact qualified owner
    // in Module.name and the public Function subject, even when their root's
    // link symbol is bare. This does not infer an identity for any callee.
    let original_unit = matches!(&public.subject,
        crate::BundleSubject::Function { crate_name, path }
            if crate_name == &context.crate_name && path == &context.path)
        && context.path == native.module.name
        && original.display_path.is_none()
        && !original.name.contains("::")
        && context.path.rsplit("::").next() == Some(original.name.as_str());
    if (!exact && !original_unit)
        || (context.path != native.module.name && context.path != identity)
    {
        return Err(
            "selected postcondition context differs from the original native unit/function".into(),
        );
    }
    Ok(())
}
