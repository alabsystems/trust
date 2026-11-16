//! Recheck carried original-source theorems before general IR loses its proof channels.
//!
//! Source identities come from this crate's checked island environment and the
//! original LCNF declarations. A producer record cannot select either its source
//! or the emitted function. These value checks confer no carrier/body license.

use std::collections::{HashMap, HashSet};

use clean_compiler::emit_trust_ir_tv::TvMintReport;
use clean_kernel::{ConstantKind, Declaration, DeclarationVerification, Environment, Name};
use clean_reflect::denote::{RecordVocab, denote_function, denote_source_with_requirements};
use trust_ir::proof::{ObligationKind, ProofStatus};
use trust_ir::{BodyGate, FuncId, Module, Ty};

#[cfg(test)]
#[path = "source_equations/tests.rs"]
mod tests;

/// General publication retains no proof authority. A mint-time body gate cites
/// the obligations being removed, so it must be withheld at the same boundary.
pub(super) fn strip_for_general(module: &mut Module) -> Result<(), String> {
    module.proof_obligations.clear();
    module.proof_certificates.clear();
    module.obligation_diagnostics.clear();
    for function in &mut module.functions {
        function.proofs.clear();
        function.summary = None;
        function.source_provenance = None;
        function.body_gate = if function.is_declaration() { None } else { Some(BodyGate::Ungated) };
    }
    let errors = trust_ir_build::validate_module(module);
    if errors.is_empty() {
        Ok(())
    } else {
        Err(format!("claim-free module failed validation: {:?}", &errors[..errors.len().min(3)]))
    }
}

/// `expected` is captured before calling the producer: exact emitted symbol and
/// typed source name. The caller has already validated the complete module.
pub(super) fn recheck(
    module: &Module,
    environment: &Environment,
    expected: &[(String, Name)],
    report: &TvMintReport,
) -> Result<usize, String> {
    let mut sources = HashSet::new();
    let mut symbols = HashMap::new();
    for (symbol, source) in expected {
        if !sources.insert(source) || symbols.insert(symbol.as_str(), source).is_some() {
            return Err("ambiguous original-source/function mapping".to_string());
        }
    }

    let certified: HashSet<FuncId> = module
        .proof_obligations
        .iter()
        .filter(|row| {
            row.kind == ObligationKind::TranslationValidation
                && row.status == ProofStatus::Certified
        })
        .filter_map(|row| row.function)
        .collect();
    let mut functions = HashMap::new();
    let mut emitted_symbols = HashSet::new();
    let mut certified_symbols = HashSet::new();
    let mut required = HashSet::new();
    let records = RecordVocab::from_module(module);
    for function in &module.functions {
        let Some(source) = symbols.get(function.name.as_str()) else { continue };
        if !emitted_symbols.insert(function.name.as_str())
            || functions.insert(function.id, *source).is_some()
        {
            return Err("ambiguous emitted function for original source".to_string());
        }
        if function.is_declaration() {
            return Err("expected original source has no emitted body".to_string());
        }
        if !certified.contains(&function.id) {
            continue;
        }
        certified_symbols.insert(function.name.as_str());
        let signature = module
            .func_types
            .get(function.ty.as_usize())
            .ok_or_else(|| "certified source function has no actual signature".to_string())?;
        if !matches!(signature.returns.as_slice(), [Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64]) {
            continue;
        }
        let emitted = denote_function(module, function)
            .map_err(|e| format!("certified original-source body cannot be inspected: {e}"))?;
        let definition = environment
            .get_const(source)
            .and_then(|info| info.value.as_ref())
            .ok_or_else(|| "expected original source has no accepted value".to_string())?;
        // Derive the requirement from actual accepted source and actual emitted
        // body, never from a record's claimed coverage or report.certified names.
        let source_model = denote_source_with_requirements(
            definition,
            emitted.width,
            &emitted.callees,
            &records,
            Some(environment),
        )
        .map_err(|e| format!("certified original-source requirement cannot be inspected: {e}"))?;
        if source_model.requires_original_source_equation {
            required.insert(function.id);
        }
    }
    if emitted_symbols.len() != symbols.len() {
        return Err("an expected original source has no emitted function".to_string());
    }
    let report_symbols: HashSet<&str> = report.certified.iter().map(String::as_str).collect();
    if report_symbols.len() != report.certified.len() || report_symbols != certified_symbols {
        return Err("producer certification labels disagree with the independently checked module"
            .to_string());
    }

    if report.source_equations.is_empty() {
        if !required.is_empty() {
            return Err("certified propositional source bodies lost their original-source proofs"
                .to_string());
        }
        if report.final_module_digest.is_some() {
            return Err("module binding has no carried original-source theorem".to_string());
        }
        return Ok(0);
    }
    if trust_ir_build::wire_identity_blocker(module).is_some() {
        return Err(
            "original-source transport has no canonical complete-module identity".to_string()
        );
    }
    if report.final_module_digest.as_ref() != Some(&Ok(module.stable_digest())) {
        return Err("original-source transport describes a different final module".to_string());
    }

    let mut seen = HashSet::new();
    for record in &report.source_equations {
        let source = functions.get(&record.function).ok_or_else(|| {
            "carried theorem names no externally mapped original function".to_string()
        })?;
        if *source != &record.source
            || !certified.contains(&record.function)
            || !seen.insert(record.function)
        {
            return Err("duplicate, unminted or wrongly mapped original-source theorem".to_string());
        }
        let proposed = Declaration::Theorem {
            name: record.theorem_name.clone(),
            level_params: record.level_params.clone(),
            type_: record.type_.clone(),
            value: record.value.clone(),
        };
        let checked = trust_ir_build::check_uint_source_value_equation(
            module,
            record.function,
            environment,
            source,
            &proposed,
        )
        .map_err(|e| format!("independent original-source replay refused: {e}"))?;
        if checked.source_closure_digest() != &record.source_closure_digest {
            return Err("original-source environment differs from the carried closure".to_string());
        }
        // Replay deliberately uses a fresh theorem name. Its equation closure
        // cannot equal the producer-named closure merely by sharing a proof.
        // Check that distinct identity in an isolated original environment.
        let mut producer_named = environment.clone();
        if producer_named.get_const(&record.theorem_name).is_some() {
            return Err(
                "producer theorem collides with the accepted source environment".to_string()
            );
        }
        producer_named
            .add_decl(proposed)
            .map_err(|e| format!("producer-named theorem replay refused: {e}"))?;
        let retained = producer_named
            .get_const(&record.theorem_name)
            .ok_or_else(|| "producer-named theorem was not retained".to_string())?;
        if producer_named.declaration_verification(&record.theorem_name)
            != Some(DeclarationVerification::FullKernelCheck)
            || retained.kind != ConstantKind::Theorem
            || retained.type_ != record.type_
            || retained.value.as_ref() != Some(&record.value)
            || producer_named.closure_digest(&record.theorem_name).ok()
                != Some(record.equation_closure_digest)
        {
            return Err("producer-named theorem closure differs from carried identity".to_string());
        }
    }
    if !required.is_subset(&seen) {
        return Err("a certified propositional source body has no independently replayed theorem"
            .to_string());
    }
    Ok(seen.len())
}
