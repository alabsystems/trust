// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Compiler-session custody for the explicit Clean Compiler API. Candidate ids
//! permit assembly only; live tokens never leave the handoff callback and are
//! checked again against the actual codegen module and CER producer binding.

use std::collections::{BTreeMap, BTreeSet};

use rustc_middle::ty::TyCtxt;
use trust_cg_bridge::f1_compile::{CleanCodegenAdmission, F1CompileInput};
use trust_clean_ir_gate::CodegenRelocation;
use trust_ir::value::FuncId;
use trust_ir::{Linkage, Module, Producer, Visibility};
use trust_thir_lower::{AssembledCrateModuleForCodegen, CleanLedgerSession};

/// Read the current Session's ledger, authenticate its actual producer rows,
/// and retain only rows already judged conserved. This data is not a license.
pub(crate) fn candidates(tcx: TyCtxt<'_>, producer: &Module) -> Result<BTreeSet<FuncId>, String> {
    let session = CleanLedgerSession::of(tcx.sess);
    let mut ids =
        tcx.sess.with_trust_compiler_state::<AssembledCrateModuleForCodegen, _>(|handoff| {
            let mut ids = BTreeSet::new();
            for row in handoff.clean_ledger(session)? {
                row.authenticate_in(producer)?;
                ids.insert(row.func_id());
            }
            Ok::<_, String>(ids)
        })?;
    if !ids.is_empty() {
        let conserved = trust_thir_lower::effect_conservation::conserved_function_ids(tcx.sess)?;
        ids.retain(|id| conserved.contains(id));
    }
    Ok(ids)
}

/// Invoke the consumer while the current Session still owns every token.
/// `placements` comes from the compiler's work/residue identity tables, rather
/// than accepting the candidate body's own linkage/visibility as authority.
pub(crate) fn with_admissions<R>(
    tcx: TyCtxt<'_>,
    input: &F1CompileInput<'_>,
    placements: &BTreeMap<FuncId, (Linkage, Visibility)>,
    consume: impl FnOnce(&[CleanCodegenAdmission<'_>]) -> R,
) -> Result<R, String> {
    if !input
        .m_cg
        .functions
        .iter()
        .any(|f| !f.is_declaration() && f.producer == Some(Producer::Clean))
    {
        return Ok(consume(&[]));
    }
    let session = CleanLedgerSession::of(tcx.sess);
    let conserved = trust_thir_lower::effect_conservation::conserved_function_ids(tcx.sess)?;
    tcx.sess.with_trust_compiler_state::<AssembledCrateModuleForCodegen, _>(|handoff| {
        let ledger = handoff.clean_ledger(session)?;
        let mut admissions = Vec::new();
        for function in input
            .m_cg
            .functions
            .iter()
            .filter(|f| !f.is_declaration() && f.producer == Some(Producer::Clean))
        {
            let binding = input
                .bodies
                .get(&function.name)
                .ok_or_else(|| format!("Clean body `{}` has no producer binding", function.name))?;
            let producer = input
                .producers
                .get(binding.producer)
                .ok_or_else(|| format!("Clean body `{}` has no producer module", function.name))?;
            let row = ledger.iter().find(|row| row.func_id() == binding.func).ok_or_else(|| {
                format!("Clean body `{}` has no current-Session carrier token", function.name)
            })?;
            if !conserved.contains(&row.func_id()) {
                return Err(format!(
                    "Clean body `{}` has no conserved current-Session source",
                    function.name
                ));
            }
            row.authenticate_in(&producer.module)?;
            let &(linkage, visibility) = placements.get(&row.func_id()).ok_or_else(|| {
                format!("Clean body `{}` has no compiler-owned placement", function.name)
            })?;
            admissions.push(CleanCodegenAdmission::checked(
                row.published(),
                &producer.module,
                row.func_id(),
                input.m_cg,
                CodegenRelocation { function_id: function.id, linkage, visibility },
            )?);
        }
        Ok(consume(&admissions))
    })
}
