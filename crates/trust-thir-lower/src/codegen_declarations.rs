//! Immutable declaration facts retained from the canonical crate finalizer.
//!
//! This is a read-only identity projection, never body admission, a codegen
//! licence or a proof grade. Only crate_module can construct the source records.
//! Rows retain the complete original assembly and checked publication images.
//! A projection exists only while its complete Function and FuncTy still match
//! the actual current handoff, including after conservation withdraws bodies.

use std::collections::BTreeMap;
use std::sync::Arc;

use trust_ir::{FuncId, FuncTy, Function, Module};

use crate::lineage::{ConcreteCalleeKey, DefinitionIdentity};

struct Entry {
    origin: Arc<Module>,
    key: String,
    definition: Option<DefinitionIdentity>,
    concrete: Option<ConcreteCalleeKey>,
    function: Function,
    signature: FuncTy,
    foreign_source: Option<crate::foreign_signature::ForeignSource>,
}

#[derive(Default)]
pub(crate) struct Declarations {
    original_handoff: Option<Arc<Module>>,
    rows: BTreeMap<FuncId, Entry>,
}

impl Declarations {
    pub(crate) fn checked(
        module: &Arc<Module>,
        records: &[crate::crate_module::CodegenDeclarationRecord],
    ) -> Result<Self, String> {
        let mut rows = BTreeMap::new();
        for record in records {
            let id = record.function().id;
            let actual = record.origin().function_by_id(id).ok_or_else(|| {
                format!("codegen declaration ledger names missing FuncId({})", id.index())
            })?;
            if !actual.is_declaration() {
                return Err(format!("retained origin FuncId({}) is not a declaration", id.index()));
            }
            if actual != record.function()
                || record.origin().func_type(actual.ty) != Some(record.signature())
            {
                return Err(format!(
                    "codegen declaration FuncId({}) differs from its retained name/type/content",
                    id.index()
                ));
            }
            let entry = Entry {
                origin: Arc::clone(record.origin()),
                key: record.key().to_owned(),
                definition: record.definition(),
                concrete: record.concrete_key().cloned(),
                function: actual.clone(),
                signature: record.signature().clone(),
                foreign_source: record.foreign_source().cloned(),
            };
            if rows.insert(id, entry).is_some() {
                return Err(format!("codegen declaration ledger repeats FuncId({})", id.index()));
            }
        }
        Ok(Self { original_handoff: Some(Arc::clone(module)), rows })
    }

    pub(crate) fn get<'a>(
        &'a self,
        module: &'a Arc<Module>,
        id: FuncId,
    ) -> Option<Declaration<'a>> {
        let original_handoff = self.original_handoff.as_ref()?;
        let entry = self.rows.get(&id)?;
        let actual = module.function_by_id(id)?;
        // Checked later joins keep their previous behavior. A changed/resolved
        // declaration simply supplies no ordinary replacement projection.
        if !actual.is_declaration()
            || actual != &entry.function
            || module.func_type(actual.ty) != Some(&entry.signature)
        {
            return None;
        }
        Some(Declaration { module, original_handoff, entry })
    }
}

/// Non-admitting facts of one declaration in the actual immutable handoff.
/// No public constructor, writable field, mutable reference or admission bit.
pub struct Declaration<'a> {
    module: &'a Arc<Module>,
    original_handoff: &'a Arc<Module>,
    entry: &'a Entry,
}

impl Declaration<'_> {
    /// The exact immutable module, including the declaration's table context.
    pub fn module(&self) -> &Arc<Module> {
        self.module
    }

    /// The complete original assembly image where the typed facts were minted.
    /// A later transformed image never silently inherits this provenance.
    pub fn origin_module(&self) -> &Arc<Module> {
        &self.entry.origin
    }

    /// The complete checked publication before conservation's body withdrawal.
    /// Withdrawn bodies gain no declaration identity through this projection.
    pub fn original_handoff_module(&self) -> &Arc<Module> {
        self.original_handoff
    }

    /// The complete original declaration, including its exact ID, name and attrs.
    pub fn function(&self) -> &Function {
        &self.entry.function
    }

    /// The exact signature in that module, never inferred from arity or width.
    pub fn signature(&self) -> &FuncTy {
        &self.entry.signature
    }

    /// Original producer classification key; a label, not linking authority.
    pub fn key(&self) -> &str {
        &self.entry.key
    }

    /// Actual retained stable definition, or None for an unknown declaration.
    pub fn definition(&self) -> Option<DefinitionIdentity> {
        self.entry.definition
    }

    /// Complete retained resolved instance key, or None when not established.
    pub fn concrete_key(&self) -> Option<&ConcreteCalleeKey> {
        self.entry.concrete.as_ref()
    }

    /// Full stable definition spelling, never a display path or truncated hash.
    pub fn definition_suffix(&self) -> Option<String> {
        self.entry.definition.map(DefinitionIdentity::symbol_suffix)
    }

    /// Full canonical retained instance key, including all positional arguments.
    pub fn concrete_suffix(&self) -> Option<String> {
        self.entry.concrete.as_ref().map(ConcreteCalleeKey::symbol_suffix)
    }

    /// Re-read this exact foreign Item's source signature and physical FnAbi.
    /// The result binds a declaration to an actual same-session Rust instance;
    /// it says nothing about its implementation, contracts or proof grade.
    pub fn foreign_instance<'tcx>(&self, tcx: rustc_middle::ty::TyCtxt<'tcx>)
        -> Result<rustc_middle::ty::Instance<'tcx>, String>
    {
        let source = self.entry.foreign_source.as_ref()
            .ok_or("declaration has no retained original foreign source identity")?;
        let instance = source.recheck(tcx, &self.entry.signature)?;
        let definition = crate::lineage::DefinitionIdentity::from_def_id(tcx, instance.def_id());
        if self.entry.definition != Some(definition)
            || self.entry.concrete.as_ref() != Some(&source.concrete_key(tcx))
            || self.entry.function.name != tcx.symbol_name(instance).name
        {
            return Err("foreign declaration's original stable definition or link symbol differs".into());
        }
        Ok(instance)
    }
}
