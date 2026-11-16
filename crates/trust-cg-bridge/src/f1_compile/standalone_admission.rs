//! Exact custody transport for an existing standalone kernel publication.
//! No instruction interpretation, carrier inference, or serialized authority.

use super::*;

/// An in-memory standalone publication tied to real producer/codegen modules.
#[derive(Debug)]
pub struct StandaloneCodegenAdmission<'a> {
    published: &'a PublishedStandaloneTrustIrFaithful,
    source: &'a Module,
    source_id: FuncId,
    relocation: CodegenRelocation,
}

impl<'a> StandaloneCodegenAdmission<'a> {
    /// Signatures and bodies are looked up in the supplied actual modules.
    /// The token must be retained from this source batch's successful kernel mint.
    pub fn checked(
        context: &trust_certify::lean_source_batch::AcceptedLeanSourceContext<'_>,
        published: &'a PublishedStandaloneTrustIrFaithful,
        source: &'a Module,
        source_id: FuncId,
        codegen: &Module,
        relocation: CodegenRelocation,
    ) -> Result<Self, String> {
        published.authenticate_context(context).map_err(|e| e.note().to_owned())?;
        let admission = Self { published, source, source_id, relocation };
        admission.authenticate(codegen)?;
        Ok(admission)
    }

    pub(super) fn function_id(&self) -> FuncId {
        self.relocation.function_id
    }

    fn authenticate<'m>(&self, codegen: &'m Module) -> Result<&'m Function, String> {
        if self.source.functions.iter().filter(|f| f.id == self.source_id).count() != 1
            || codegen.functions.iter().filter(|f| f.id == self.relocation.function_id).count() != 1
        {
            return Err("standalone source/codegen function id is missing or not unique".into());
        }
        let source =
            self.source.function_by_id(self.source_id).ok_or("standalone source body missing")?;
        let target = codegen
            .function_by_id(self.relocation.function_id)
            .ok_or("standalone target body missing")?;
        let source_signature = self
            .source
            .func_types
            .get(source.ty.as_usize())
            .ok_or("standalone source signature missing")?;
        let target_signature = codegen
            .func_types
            .get(target.ty.as_usize())
            .ok_or("standalone target signature missing")?;
        self.published
            .authenticate_codegen(
                source_signature,
                source,
                target_signature,
                target,
                self.relocation,
            )
            .map_err(|e| e.note().to_owned())?;
        Ok(target)
    }

    pub(super) fn check_input(&self, input: &F1CompileInput<'_>) -> Result<(), String> {
        let target = self.authenticate(input.m_cg)?;
        let binding =
            input.bodies.get(&target.name).ok_or("standalone output-gate binding missing")?;
        let producer = input
            .producers
            .get(binding.producer)
            .ok_or("standalone output-gate producer missing")?;
        if producer.module.functions.iter().filter(|f| f.id == binding.func).count() != 1 {
            return Err(
                "standalone output-gate producer function id is missing or not unique".into()
            );
        }
        let actual = producer
            .module
            .function_by_id(binding.func)
            .ok_or("standalone output-gate body missing")?;
        let expected =
            self.source.function_by_id(self.source_id).ok_or("standalone retained body missing")?;
        if actual != expected
            || producer.module.func_types.get(actual.ty.as_usize())
                != self.source.func_types.get(expected.ty.as_usize())
            || producer.symbols.get(&binding.func) != Some(&target.name)
        {
            return Err(
                "standalone output-gate producer differs from retained kernel subject".into()
            );
        }
        Ok(())
    }
}
