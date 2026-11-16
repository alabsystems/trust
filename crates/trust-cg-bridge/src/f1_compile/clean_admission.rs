// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! In-memory Clean admission, separate from a freely writable body-gate stamp.
//! The ordinary API supplies an empty boundary. Only the explicit Clean API
//! can supply kernel-bound publications, and every use rechecks the actual
//! codegen body and the producer selected for the output gate.

use trust_cg_lower::CodegenLicensePolicy;
#[cfg(feature = "clean-codegen")]
use trust_clean_ir_gate::standalone::{
    PublishedStandaloneTrustIrFaithful, STANDALONE_CODEGEN_AUTHORITY,
};
#[cfg(feature = "clean-codegen")]
use trust_clean_ir_gate::{
    CLEAN_CARRIER_GATE_AUTHORITY, CodegenRelocation, PublishedTrustIrFaithful, authenticate_codegen,
};
use trust_ir::value::FuncId;
#[cfg(feature = "clean-codegen")]
use trust_ir::{Function, Module};

use super::{CensusRow, F1CompileInput};

#[cfg(feature = "clean-codegen")]
#[path = "standalone_admission.rs"]
mod standalone_admission;
#[cfg(feature = "clean-codegen")]
pub use standalone_admission::StandaloneCodegenAdmission;

/// A kernel-bound publication and its compiler-owned codegen placement.
///
/// Private fields, no deserializer, and a borrow of the original publication
/// prevent a stored stamp from becoming a permission. This is a codegen
/// license only: the unchanged output gate still decides whether bytes ship.
#[cfg(feature = "clean-codegen")]
#[derive(Debug)]
pub struct CleanCodegenAdmission<'a> {
    published: &'a PublishedTrustIrFaithful,
    source: &'a Module,
    source_id: FuncId,
    relocation: CodegenRelocation,
}

#[cfg(feature = "clean-codegen")]
impl<'a> CleanCodegenAdmission<'a> {
    /// Authenticate using signatures looked up in the actual modules. In rustc,
    /// `published` must come from the current Session's authenticated ledger;
    /// the library has no rustc Session and does not infer custody from a stamp.
    pub fn checked(
        published: &'a PublishedTrustIrFaithful,
        source: &'a Module,
        source_id: FuncId,
        codegen: &Module,
        relocation: CodegenRelocation,
    ) -> Result<Self, String> {
        let admission = Self { published, source, source_id, relocation };
        admission.authenticate(codegen)?;
        Ok(admission)
    }

    fn authenticate<'m>(&self, codegen: &'m Module) -> Result<&'m Function, String> {
        let source = self
            .source
            .function_by_id(self.source_id)
            .ok_or_else(|| "Clean admission names no published function".to_string())?;
        let target = codegen
            .function_by_id(self.relocation.function_id)
            .ok_or_else(|| "Clean admission names no codegen function".to_string())?;
        let source_signature = self
            .source
            .func_types
            .get(source.ty.as_usize())
            .ok_or_else(|| "Clean admission names no published signature".to_string())?;
        let target_signature = codegen
            .func_types
            .get(target.ty.as_usize())
            .ok_or_else(|| "Clean admission names no codegen signature".to_string())?;
        authenticate_codegen(
            self.published,
            source_signature,
            source,
            target_signature,
            target,
            self.relocation,
        )
        .map_err(|refusal| refusal.note().to_string())?;
        Ok(target)
    }

    fn check_input(&self, input: &F1CompileInput<'_>) -> Result<(), String> {
        let target = self.authenticate(input.m_cg)?;
        if input.m_cg.functions.iter().filter(|f| f.id == target.id).count() != 1 {
            return Err("Clean codegen function id is not unique".into());
        }
        let binding = input
            .bodies
            .get(&target.name)
            .ok_or_else(|| "Clean codegen body has no output-gate producer binding".to_string())?;
        let producer = input
            .producers
            .get(binding.producer)
            .ok_or_else(|| "Clean output-gate binding names no producer module".to_string())?;
        let actual_source = producer
            .module
            .function_by_id(binding.func)
            .ok_or_else(|| "Clean output-gate binding names no producer body".to_string())?;
        let expected_source = self
            .source
            .function_by_id(self.source_id)
            .ok_or_else(|| "Clean admission lost its published source body".to_string())?;
        if actual_source != expected_source
            || producer.module.func_types.get(actual_source.ty.as_usize())
                != self.source.func_types.get(expected_source.ty.as_usize())
            || producer.symbols.get(&binding.func) != Some(&target.name)
        {
            return Err(
                "Clean output-gate producer differs from the authenticated publication".into()
            );
        }
        Ok(())
    }
}

#[derive(Clone, Copy)]
pub(super) struct CleanBoundary<'a> {
    #[cfg(feature = "clean-codegen")]
    admissions: &'a [CleanCodegenAdmission<'a>],
    #[cfg(feature = "clean-codegen")]
    standalone: &'a [StandaloneCodegenAdmission<'a>],
    #[cfg(not(feature = "clean-codegen"))]
    marker: std::marker::PhantomData<&'a ()>,
}

impl<'a> CleanBoundary<'a> {
    pub(super) fn none() -> Self {
        Self {
            #[cfg(feature = "clean-codegen")]
            admissions: &[],
            #[cfg(feature = "clean-codegen")]
            standalone: &[],
            #[cfg(not(feature = "clean-codegen"))]
            marker: std::marker::PhantomData,
        }
    }

    #[cfg(feature = "clean-codegen")]
    pub(super) fn new(admissions: &'a [CleanCodegenAdmission<'a>]) -> Self {
        Self { admissions, standalone: &[] }
    }

    #[cfg(feature = "clean-codegen")]
    pub(super) fn standalone(standalone: &'a [StandaloneCodegenAdmission<'a>]) -> Self {
        Self { admissions: &[], standalone }
    }

    pub(super) fn contains(self, id: FuncId) -> bool {
        #[cfg(feature = "clean-codegen")]
        {
            self.admissions.iter().any(|a| a.relocation.function_id == id)
                || self.standalone.iter().any(|a| a.function_id() == id)
        }
        #[cfg(not(feature = "clean-codegen"))]
        {
            let _ = id;
            false
        }
    }

    pub(super) fn license(self, ordinary: CodegenLicensePolicy) -> CodegenLicensePolicy {
        #[cfg(feature = "clean-codegen")]
        {
            // Called only after exact typed custody and boundary checks.
            let mut license = ordinary;
            if !self.admissions.is_empty() {
                license = license.with_recognized_authority(CLEAN_CARRIER_GATE_AUTHORITY);
            }
            if !self.standalone.is_empty() {
                license = license.with_recognized_authority(STANDALONE_CODEGEN_AUTHORITY);
            }
            return license;
        }
        #[cfg(not(feature = "clean-codegen"))]
        ordinary
    }

    pub(super) fn check_input(self, input: &F1CompileInput<'_>) -> Vec<CensusRow> {
        #[cfg(feature = "clean-codegen")]
        {
            use std::collections::BTreeSet;
            let mut seen = BTreeSet::new();
            let mut rows = Vec::new();
            for admission in self.admissions {
                let id = admission.relocation.function_id;
                let result = if seen.insert(id) {
                    admission.check_input(input)
                } else {
                    Err("Clean admission repeats a codegen function id".into())
                };
                if let Err(detail) = result {
                    rows.push(CensusRow {
                        func: Some(id),
                        symbol: input
                            .m_cg
                            .function_by_id(id)
                            .map(|f| f.name.clone())
                            .unwrap_or_default(),
                        variant: "CleanAdmissionMismatch".into(),
                        detail,
                    });
                }
            }
            for admission in self.standalone {
                let id = admission.function_id();
                let result = if seen.insert(id) {
                    admission.check_input(input)
                } else {
                    Err("standalone admission repeats a codegen function id".into())
                };
                if let Err(detail) = result {
                    rows.push(CensusRow {
                        func: Some(id),
                        symbol: input
                            .m_cg
                            .function_by_id(id)
                            .map(|f| f.name.clone())
                            .unwrap_or_default(),
                        variant: "StandaloneAdmissionMismatch".into(),
                        detail,
                    });
                }
            }
            if !self.admissions.is_empty() || !self.standalone.is_empty() {
                for function in input.m_cg.functions.iter().filter(|f| !f.is_declaration()) {
                    if function.producer != Some(trust_ir::Producer::Clean)
                        && matches!(&function.body_gate, Some(trust_ir::BodyGate::Gated { authority, .. })
                            if authority == CLEAN_CARRIER_GATE_AUTHORITY || authority == STANDALONE_CODEGEN_AUTHORITY)
                    {
                        rows.push(CensusRow {
                            func: Some(function.id),
                            symbol: function.name.clone(),
                            variant: "CleanAuthorityOnOtherProducer".into(),
                            detail: "a Clean permission cannot license another producer's stamp"
                                .into(),
                        });
                    }
                }
            }
            rows
        }
        #[cfg(not(feature = "clean-codegen"))]
        {
            let _ = input;
            Vec::new()
        }
    }
}
