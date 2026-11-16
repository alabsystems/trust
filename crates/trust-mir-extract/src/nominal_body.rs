// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Completed, immutable compiler query snapshots with actual parameter custody.
//! This never demands MIR, borrows a Steal, accepts a supplied body/function,
//! reconstructs an earlier phase, or grants source/body proof authority.

use rustc_middle::mir::{self, Body, MirPhase, RuntimePhase};
use rustc_middle::query::erase::restore_val;
use trust_types::VerifiableFunction;

use super::nominal_parameter::NominalParameterObservation;

pub struct NominalBodyObservation<'tcx> {
    nominal: NominalParameterObservation<'tcx>,
    body: &'tcx Body<'tcx>,
    argument_local: mir::Local,
    source_attributes: &'tcx [rustc_attr_ir::Attribute],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NominalBodyRefusal {
    MirBuilding,
    SnapshotNotCached,
    SnapshotUnavailable,
    SnapshotPhase(MirPhase),
    SourceIdentity,
    BodyBound,
    BodyStructure,
    ArgumentPopulation,
    ArgumentType,
    ReturnType,
    SourceBodyUnavailable,
    SourceMetadataBound,
    AuthoredContracts,
}

impl<'tcx> NominalBodyObservation<'tcx> {
    pub fn nominal(&self) -> &NominalParameterObservation<'tcx> {
        &self.nominal
    }
    pub fn body(&self) -> &'tcx Body<'tcx> {
        self.body
    }
    pub fn argument_local(&self) -> mir::Local {
        self.argument_local
    }
    pub fn observed_phase(&self) -> MirPhase {
        self.body.phase
    }
    pub fn observed_pass_count(&self) -> usize {
        self.body.pass_count
    }
    pub fn source_attributes(&self) -> &'tcx [rustc_attr_ir::Attribute] {
        self.source_attributes
    }
    /// This first profile checks actual HIR and legacy attribute populations.
    /// It does NOT replace authored clauses by true or discard unsupported ones.
    pub fn authored_clause_count(&self) -> usize {
        0
    }
    /// Existing faithful extractor; the returned cloneable function is DATA,
    /// not this live observation and not a source-to-view preservation theorem.
    pub fn extract_faithful(&self) -> VerifiableFunction {
        crate::extract_function_faithful(self.nominal.context(), self.body)
    }
}

/// Observe ONLY a completed canonical immutable query result. The compiler
/// producer must have prepared that result at a legal pre-steal seam. A missing
/// or in-progress result refuses instead of starting/waiting on a MIR query.
/// The existing provider can cache optimized fallback bodies; those refuse.
/// A retained genuine elaborated snapshot remains valid after its Steal dies.
/// Neither this query provenance nor phase/pass_count authenticates historical
/// TrustVerify-input JSON (a different producer/pass boundary).
pub fn observe_cached_nominal_body<'tcx>(
    nominal: NominalParameterObservation<'tcx>,
) -> Result<NominalBodyObservation<'tcx>, NominalBodyRefusal> {
    use NominalBodyRefusal as Refuse;
    if crate::ctfe_reentrancy::frozen() {
        return Err(Refuse::MirBuilding);
    }
    let tcx = nominal.context();
    let owner = nominal.owner();
    let cache = &tcx.query_system.query_vtables.mir_for_trust_verification.cache;
    let (erased, index) = cache.lookup(&owner).ok_or(Refuse::SnapshotNotCached)?;
    // Same cache-hit bookkeeping as query::calls::try_get_cached. In particular
    // retain the actual dependency edge; no untracked cached-body authority.
    tcx.prof.query_cache_hit(index.into());
    tcx.dep_graph.read_index(index);
    let body: Option<&'tcx Body<'tcx>> = restore_val(erased);
    let body = body.ok_or(Refuse::SnapshotUnavailable)?;
    if body.phase != MirPhase::Runtime(RuntimePhase::PostCleanup) {
        return Err(Refuse::SnapshotPhase(body.phase));
    }
    if body.source.promoted.is_some()
        || !matches!(body.source.instance, rustc_middle::ty::InstanceKind::Item(id) if id == owner.to_def_id())
        || body.tainted_by_errors.is_some()
        || body.coroutine.is_some()
    {
        return Err(Refuse::SourceIdentity);
    }
    if body.local_decls.len() > 4096 || body.basic_blocks.len() > 1024 {
        return Err(Refuse::BodyBound);
    }
    let mut statements = 0usize;
    for block in body.basic_blocks.iter() {
        if block.terminator.is_none() {
            return Err(Refuse::BodyStructure);
        }
        statements = statements.checked_add(block.statements.len()).ok_or(Refuse::BodyBound)?;
        if statements > 8192 {
            return Err(Refuse::BodyBound);
        }
    }
    let signature = tcx.fn_sig(owner).instantiate_identity().skip_normalization();
    if !signature.bound_vars().is_empty() {
        return Err(Refuse::ArgumentPopulation);
    }
    let signature = signature.skip_binder();
    if body.spread_arg.is_some()
        || body.arg_count != signature.inputs().len()
        || body.args_iter().len() != body.arg_count
    {
        return Err(Refuse::ArgumentPopulation);
    }
    if body.local_decls.get(mir::RETURN_PLACE).is_none_or(|decl| decl.ty != signature.output()) {
        return Err(Refuse::ReturnType);
    }
    let mut argument_local = None;
    for (ordinal, (local, source_ty)) in body.args_iter().zip(signature.inputs()).enumerate() {
        if body.local_decls.get(local).is_none_or(|decl| decl.ty != *source_ty) {
            return Err(Refuse::ArgumentType);
        }
        if ordinal == nominal.argument() {
            if *source_ty != nominal.source_ty() {
                return Err(Refuse::ArgumentType);
            }
            argument_local = Some(local);
        }
    }
    let argument_local = argument_local.ok_or(Refuse::ArgumentPopulation)?;
    let hir_body = tcx.hir_maybe_body_owned_by(owner).ok_or(Refuse::SourceBodyUnavailable)?;
    if hir_body.contract.is_some() {
        return Err(Refuse::AuthoredContracts);
    }
    let attrs = tcx.hir_attrs(tcx.local_def_id_to_hir_id(owner));
    if attrs.len() > 256 {
        return Err(Refuse::SourceMetadataBound);
    }
    for attr in attrs {
        let path = match attr {
            rustc_attr_ir::Attribute::Tool(item) | rustc_attr_ir::Attribute::DeriveHelper(item) => {
                &item.path.segments
            }
            rustc_attr_ir::Attribute::Parsed(_) => continue,
        };
        if path.len() > 64 {
            return Err(Refuse::SourceMetadataBound);
        }
        if let [namespace, name] = path.as_ref() {
            if trust_types::trust_attr_namespace::contract_kind_of_attr_path(&[
                namespace.as_str(),
                name.as_str(),
            ])
            .is_some()
            {
                return Err(Refuse::AuthoredContracts);
            }
        }
    }
    Ok(NominalBodyObservation { nominal, body, argument_local, source_attributes: attrs })
}
