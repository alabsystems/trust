//! Sealed R-body installation into an actual retained handoff declaration.
//!
//! A symbol locates a candidate only. The session's immutable ordinary ledger,
//! actual Rust stable definition and complete canonical instance key bind it.
//! No caller supplies an admission bit, identity resolver or replacement slot.

use std::sync::Arc;

use rustc_middle::ty::{self, TyCtxt};
use trust_ir::{FuncId, FuncTy, Function, Module, Producer};

use super::super::upstream_entry;

/// Private-content installation binding, constructed only from actual session
/// handoff facts and the sealed upstream body's own admitted Instance.
pub(crate) struct BoundDeclaration {
    base: Arc<Module>,
    original: Function,
    signature: FuncTy,
    guest: Module,
}

impl BoundDeclaration {
    /// Recheck the retained installation premise against the actual immutable
    /// handoff and the sealed upstream module after installation. This is data
    /// custody only: it grants no exception to codegen's closure equality rule.
    pub(super) fn check_retained(
        &self,
        base: &Module,
        guest: &Module,
        installed: FuncId,
    ) -> Result<(), String> {
        if !std::ptr::eq(self.base.as_ref(), base)
            || self.original.id != installed
            || !self.original.is_declaration()
            || base.function_by_id(installed) != Some(&self.original)
            || base.func_type(self.original.ty) != Some(&self.signature)
            || guest != &self.guest
        {
            return Err("retained declaration installation premise differs from its original handoff or admitted body".into());
        }
        Ok(())
    }

    /// Recheck the exact content immediately at the existing sole appender.
    pub(super) fn slot(&self, host: &Module, guest: &Module) -> Result<FuncId, String> {
        if guest != &self.guest {
            return Err("bound declaration names another admitted upstream body image".into());
        }
        super::tables_unchanged(&self.base, host)?;
        if host.functions.iter().filter(|f| f.name == self.original.name).count() != 1
            || !self.original.is_declaration()
            || !self.original.proofs.is_empty()
            || host.proof_obligations.iter().any(|o| o.function == Some(self.original.id))
            || host.function_by_id(self.original.id) != Some(&self.original)
            || host.func_type(self.original.ty) != Some(&self.signature)
            || self.base.function_by_id(self.original.id) != Some(&self.original)
        {
            return Err("bound declaration no longer matches its original handoff content".into());
        }
        Ok(self.original.id)
    }
}

pub(super) fn bind_upstream<'tcx>(
    tcx: TyCtxt<'tcx>,
    base: &Arc<Module>,
    host: &Module,
    guest: &upstream_entry::UpstreamBody<'tcx>,
) -> Result<Option<BoundDeclaration>, String> {
    let instance = guest.admitted().instance();
    let ty::InstanceKind::Item(def) = instance.def else {
        return Err("upstream declaration binding requires an admitted ordinary Item".into());
    };
    let body = guest
        .module()
        .function_by_id(FuncId::new(0))
        .ok_or("admitted upstream body has no FuncId0")?;
    let symbol = tcx.symbol_name(instance).name;
    if body.name != symbol || def.is_local() || !tcx.should_codegen_locally(instance) {
        return Err("upstream declaration binding differs from its actual admitted instance".into());
    }
    let candidates: Vec<_> = host.functions.iter().filter(|f| f.name == symbol).collect();
    let Some(candidate) = candidates.first() else {
        return Ok(None);
    };
    if candidates.len() != 1 || !candidate.is_declaration() {
        return Err(format!("upstream symbol `{symbol}` already names a body or ambiguous rows"));
    }
    let hash = tcx.def_path_hash(def);
    if hash.stable_crate_id().as_u64() != tcx.stable_crate_id(def.krate).as_u64() {
        return Err("upstream declaration's actual stable crate identities disagree".into());
    }
    let definition =
        format!("{:016x}{:016x}", hash.stable_crate_id().as_u64(), hash.local_hash().as_u64());
    let concrete = trust_thir_lower::metadata_site::canonical_suffix(tcx, instance)
        .map_err(|e| e.to_string())?;
    tcx.sess.with_trust_compiler_state::<trust_thir_lower::AssembledCrateModuleForCodegen, _>(
        |handoff| {
            let projection = handoff
                .declaration(candidate.id)
                .ok_or("upstream symbol has no exact retained handoff declaration identity")?;
            if !Arc::ptr_eq(projection.module(), base) {
                return Err("upstream declaration comes from another handoff module".into());
            }
            checked_projection(base, host, guest.module(), &projection, &definition, &concrete)
                .map(Some)
        },
    )
}

fn checked_projection(
    base: &Arc<Module>,
    host: &Module,
    guest: &Module,
    projection: &trust_thir_lower::codegen_declarations::Declaration<'_>,
    definition: &str,
    concrete: &str,
) -> Result<BoundDeclaration, String> {
    let original = projection.function();
    let body = guest.function_by_id(FuncId::new(0)).ok_or("guest body absent")?;
    let signature = guest.func_type(body.ty).ok_or("guest signature absent")?;
    check_identity_facts(
        projection.definition_suffix().as_deref(),
        projection.concrete_suffix().as_deref(),
        definition,
        concrete,
    )?;
    super::tables_unchanged(projection.original_handoff_module(), base)?;
    if !original.is_declaration()
        || !producer_facts_compatible(original.producer.as_ref(), body.producer.as_ref())
        || original.name != body.name
        || original.calling_conv != body.calling_conv
        || projection.signature() != signature
        || original.attrs != body.attrs
        || original.summary.is_some()
        || !original.proofs.is_empty()
        || base.proof_obligations.iter().any(|o| o.function == Some(original.id))
        || host.proof_obligations.iter().any(|o| o.function == Some(original.id))
        || host.function_by_id(original.id) != Some(original)
        || base.function_by_id(original.id) != Some(original)
        || guest.target_info != base.target_info
    {
        return Err(
            "retained upstream declaration/body signature, attributes or exact content disagree"
                .into(),
        );
    }
    Ok(BoundDeclaration {
        base: Arc::clone(base),
        original: original.clone(),
        signature: signature.clone(),
        guest: guest.clone(),
    })
}

fn producer_facts_compatible(recorded: Option<&Producer>, admitted: Option<&Producer>) -> bool {
    // Canonical nonlocal ordinary declarations have producer None: unrecorded,
    // never guessed. The sealed R entry establishes the actual body's TRust
    // producer independently; a recorded contradictory producer still refuses.
    admitted == Some(&Producer::TRust) && (recorded.is_none() || recorded == admitted)
}

fn check_identity_facts(
    recorded_definition: Option<&str>,
    recorded_concrete: Option<&str>,
    actual_definition: &str,
    actual_concrete: &str,
) -> Result<(), String> {
    if recorded_definition != Some(actual_definition) || recorded_concrete != Some(actual_concrete)
    {
        return Err(
            "retained declaration names another stable definition or complete instance".into()
        );
    }
    Ok(())
}

#[cfg(test)]
mod tests;
