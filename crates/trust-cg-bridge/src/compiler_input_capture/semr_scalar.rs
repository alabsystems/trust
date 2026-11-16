// Copyright 2026 Andrew Yates | Apache-2.0
//! Expected canonical SemR subject derived from the independently selected
//! ORIGINAL ProducerModule, never from a proof packet or decoded capture.
//! This is input DATA, not Rust/TCX provenance or a compiler capability.
use std::collections::BTreeMap;

use clean_olean::semr_scalar::ScalarSubject;
use serde::{Deserialize, Serialize};
use trust_ir::inst::BinOp;
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{CallingConv, Constant, Endianness, Inst, Ty};

use super::{MAX_PART_BYTES, ModuleBytes};
use crate::call_event::{CerInput, ProducerBody, ProducerModule};
use crate::f1_compile::F1CompileInput;
use crate::object_replay::artifact_digest;

mod environment;
mod program;
mod program_contract;
mod scalar_contract;
mod source_contract;
mod source_binding;
pub use environment::{CanonicalScalarEnvironment, CheckedOriginalScalar, OriginalScalarPacket};
pub use program::{
    CanonicalScalarProgramEnvironment, CheckedOriginalScalarProgram, OriginalScalarProgramPacket,
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ScalarBinding {
    pub symbol: String,
    pub producer: u64,
    pub function: u32,
    pub function_type: u32,
    pub entry: u32,
    pub parameter: u32,
    pub constant: u32,
    pub sum: u32,
    pub returned: u32,
    pub module_sha256: String,
    pub literal: u64,
}

/// Non-authorizing immutable mathematical input. There is no raw-subject,
/// packet-selected byte/model, signature-only or source-token constructor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExpectedScalarInput {
    pub(super) binding: ScalarBinding,
    pub(super) subject: ScalarSubject,
}
impl ExpectedScalarInput {
    /// Read actual ORIGINAL producers from the real F1 compile request. No
    /// Compiler, interpreter, solver, proof producer or grading path is run.
    pub fn from_compile_input(input: &F1CompileInput<'_>, symbol: &str) -> Result<Self, String> {
        Self::derive(input.producers, input.bodies, symbol)
    }

    pub(super) fn from_current(input: &CerInput<'_>, symbol: &str) -> Result<Self, String> {
        Self::derive(input.producers, input.bodies, symbol)
    }

    pub fn module_bytes(&self) -> &[u8] {
        &self.subject.module_bytes
    }
    pub fn literal(&self) -> u64 {
        self.subject.literal
    }
    pub fn symbol(&self) -> &str {
        &self.binding.symbol
    }

    fn derive(
        producers: &[ProducerModule],
        bodies: &BTreeMap<String, ProducerBody>,
        symbol: &str,
    ) -> Result<Self, String> {
        let selected = bodies.get(symbol).ok_or("scalar symbol has no original producer body")?;
        let producer = producers.get(selected.producer).ok_or("scalar original producer index")?;
        let m = producer.module.as_ref();
        // Preserve the existing complete bounded Module transport first. It
        // bounds even debug/proof metadata before the canonical binary pool is
        // collected. No ignored field is re-created from a guessed template.
        let _ = ModuleBytes::capture(m)?;
        if !trust_ir_build::validate_module(m).is_empty() {
            return Err("scalar original Module validation refused".into());
        }
        if selected.func != FuncId::new(0)
            || producer.symbols.len() != 1
            || producer.symbols.get(&selected.func).map(String::as_str) != Some(symbol)
            || m.functions.len() != 1
            || m.func_types.len() != 1
            || !m.structs.is_empty()
            || !m.enums.is_empty()
            || !m.records.is_empty()
            || !m.closure_types.is_empty()
            || !m.globals.is_empty()
            || !m.types.is_empty()
            || !m.spec_modules.is_empty()
            || !m.universes.is_empty()
            || !m.predicates.is_empty()
            || !m.global_asm.is_empty()
            || !m.imports.is_empty()
            || !m.tuple_layouts.is_empty()
        {
            return Err("scalar original is outside the closed single-function/table domain".into());
        }
        let f = &m.functions[0];
        let sig = &m.func_types[0];
        let target = m.target_info.as_ref().ok_or("scalar original target is absent")?;
        if f.id != selected.func
            || f.name != symbol
            || f.ty != FuncTyId::new(0)
            || f.entry != BlockId::new(0)
            || f.blocks.len() != 1
            || f.calling_conv != CallingConv::Rust
            || sig.params != [Ty::U64]
            || sig.returns != [Ty::U64]
            || sig.is_vararg
            || sig.abi.is_some()
            || target.pointer_size != 8
            || target.endianness != Endianness::Little
        {
            return Err("scalar original function/signature/entry/convention/target differs".into());
        }
        let b = &f.blocks[0];
        if b.id != f.entry || b.params != [(ValueId::new(0), Ty::U64)] || b.body.len() != 3 {
            return Err("scalar original block/parameter/body shape differs".into());
        }
        let [constant, sum, returned] = b.body.as_slice() else {
            return Err("scalar original instruction population differs".into());
        };
        let Inst::Const { ty: Ty::U64, value: Constant::Int(literal) } = &constant.inst else {
            return Err("scalar original first instruction is not an actual U64 literal".into());
        };
        let literal = u64::try_from(*literal).map_err(|_| "scalar original literal range")?;
        if constant.results != [ValueId::new(1)]
            || sum.inst
                != (Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::U64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                })
            || sum.results != [ValueId::new(2)]
            || returned.inst != (Inst::Return { values: vec![ValueId::new(2)] })
            || !returned.results.is_empty()
        {
            return Err("scalar original Const/Add/Return operands or SSA identities differ".into());
        }
        // One existing canonical writer over the COMPLETE actual Module. No
        // root relabel, ID normalization, table projection or source rebuild.
        let mut plan = trust_ir::binary::ModuleBinaryPlan::new(m);
        if plan.encoded_len() > MAX_PART_BYTES {
            return Err("scalar canonical Module byte budget".into());
        }
        let module_bytes = plan.to_vec().map_err(|error| error.to_string())?;
        if trust_ir::binary::deserialize_module(&module_bytes).map_err(|error| error.to_string())?
            != *m
        {
            return Err("scalar canonical complete Module roundtrip differs".into());
        }
        let binding = ScalarBinding {
            symbol: symbol.into(),
            producer: u64::try_from(selected.producer)
                .map_err(|_| "scalar producer index width")?,
            function: f.id.index(),
            function_type: f.ty.index(),
            entry: f.entry.index(),
            parameter: 0,
            constant: 1,
            sum: 2,
            returned: 2,
            module_sha256: artifact_digest(&module_bytes),
            literal,
        };
        Ok(Self { binding, subject: ScalarSubject { module_bytes, literal } })
    }
}

#[cfg(test)]
mod tests;
