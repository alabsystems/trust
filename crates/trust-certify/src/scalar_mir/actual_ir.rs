//! Independent, bounded reader of an actual Trust-IR scalar body.
//!
//! This is model correspondence, not Rust-source fidelity or compiler proof
//! authority. It does not accept the native MIR-compatibility spelling's
//! assumptions or Undef-based aggregate construction. The original module,
//! including metadata and obligation rows, remains part of replay identity.

use trust_ir::{
    AssertKind, AssertOverflowOp, CallingConv, CastOp, Constant, FuncId, Inst, Module, OverflowOp,
    Ty, ValueId,
};

mod model;
mod proof;
#[cfg(test)]
mod tests;

/// Complete operational input to this deliberately fixed instruction family.
/// IDs are retained exactly; this is not an alpha-renaming or dead-code pass.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Instruction {
    Widen { result: u32, operand: u32 },
    U16 { result: u32, value: u16 },
    Bool { result: u32, value: bool },
    AddOverflow { result: u32, flag: u32, left: u32, right: u32 },
    Select { result: u32, condition: u32, yes: u32, no: u32 },
    Assert(u32),
    Return(u32),
}

/// Retains the real module bytes plus independently checked model evidence.
/// No conversion into CleanCic, source authority, or a compiler result exists.
pub struct ScalarActualIrCertificate {
    module_bytes: Vec<u8>,
    function: FuncId,
    proof: proof::Certificate,
}

impl ScalarActualIrCertificate {
    pub fn replay(&self, module: &Module, function: FuncId) -> Result<(), String> {
        if self.function != function || module_bytes(module)? != self.module_bytes {
            return Err("actual IR module/function changed since construction".into());
        }
        let code = read(module, function)?;
        self.proof.replay(&code)
    }
}

/// Read every instruction of the actual module, then kernel-check the full
/// observation for every genuine UInt8 (including the exhaustion proof).
/// Caller-supplied modules are model inputs, not authenticated source captures.
pub fn prove_actual_successor_ir(
    module: &Module,
    function: FuncId,
) -> Result<ScalarActualIrCertificate, String> {
    let code = read(module, function)?;
    let module_bytes = module_bytes(module)?;
    let proof = proof::prove(&code)?;
    Ok(ScalarActualIrCertificate { module_bytes, function, proof })
}

fn module_bytes(module: &Module) -> Result<Vec<u8>, String> {
    struct BoundedBytes(Vec<u8>);
    impl std::io::Write for BoundedBytes {
        fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
            if bytes.len() > (1024 * 1024_usize).saturating_sub(self.0.len()) {
                return Err(std::io::Error::other(
                    "actual scalar module exceeds retained-byte limit",
                ));
            }
            self.0.extend_from_slice(bytes);
            Ok(bytes.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }
    let mut bytes = BoundedBytes(Vec::new());
    serde_json::to_writer(&mut bytes, module)
        .map_err(|e| format!("actual module encoding: {e}"))?;
    Ok(bytes.0)
}

fn read(module: &Module, id: FuncId) -> Result<Vec<Instruction>, String> {
    // Bound the validator before invoking it. The initial whole-module family
    // is one function, so no unexamined sibling or callee can hide effects.
    if module.functions.len() != 1
        || module.func_types.len() != 1
        || !module.structs.is_empty()
        || !module.enums.is_empty()
        || !module.records.is_empty()
        || !module.closure_types.is_empty()
        || !module.globals.is_empty()
        || !module.types.is_empty()
        || !module.spec_modules.is_empty()
        || !module.universes.is_empty()
        || !module.predicates.is_empty()
        || !module.proof_certificates.is_empty()
        || module.proof_obligations.len() > 8
        || module.obligation_diagnostics.len() > 8
        || module.files.len() > 16
    {
        return Err("actual scalar IR requires one bounded closed function/module".into());
    }
    let function = &module.functions[0];
    if function.id != id
        || function.blocks.len() != 1
        || function.calling_conv != CallingConv::Rust
        || function.summary.is_some()
        || function.source_provenance.is_some()
        || function.attrs != Default::default()
        || !function.proofs.is_empty()
    {
        return Err(
            "actual scalar function identity, ABI, effects, or assumptions unsupported".into()
        );
    }
    let signature = module.func_types.get(function.ty.as_usize()).ok_or("missing signature")?;
    if signature.params != [Ty::U8] || signature.returns != [Ty::U16] || signature.is_vararg {
        return Err("actual scalar signature must be (u8)->u16".into());
    }
    let block = &function.blocks[0];
    if block.id != function.entry
        || block.params != [(ValueId::new(0), Ty::U8)]
        || block.body.len() != 8
    {
        return Err("actual scalar entry/SSA/instruction census differs".into());
    }
    let errors = trust_ir_build::validate_module(module);
    if !errors.is_empty() {
        return Err(format!("actual scalar module is invalid: {errors:?}"));
    }
    let mut code = Vec::new();
    for node in &block.body {
        if node.proof_context.is_some() {
            return Err("actual scalar instruction has a call proof context".into());
        }
        if !node.proofs.is_empty()
            && !(matches!(node.inst, Inst::Assert { .. })
                && node.proofs == [trust_ir::ProofAnnotation::NoOverflow])
        {
            return Err("actual scalar instruction carries an unsupported annotation".into());
        }
        let results: Vec<_> = node.results.iter().map(|v| v.0).collect();
        let instruction = match (&node.inst, results.as_slice()) {
            (
                Inst::Cast { op: CastOp::ZExt, src_ty: Ty::U8, dst_ty: Ty::U16, operand },
                [result],
            ) => Instruction::Widen { result: *result, operand: operand.0 },
            (Inst::Const { ty: Ty::U16, value: Constant::Int(value) }, [result]) => {
                Instruction::U16 {
                    result: *result,
                    value: u16::try_from(*value).map_err(|_| "non-u16 literal")?,
                }
            }
            (Inst::Const { ty: Ty::Bool, value: Constant::Bool(value) }, [result]) => {
                Instruction::Bool { result: *result, value: *value }
            }
            (
                Inst::Overflow { op: OverflowOp::AddOverflow, ty: Ty::U16, lhs, rhs },
                [result, flag],
            ) => {
                Instruction::AddOverflow { result: *result, flag: *flag, left: lhs.0, right: rhs.0 }
            }
            (Inst::Select { ty: Ty::Bool, cond, then_val, else_val }, [result]) => {
                Instruction::Select {
                    result: *result,
                    condition: cond.0,
                    yes: then_val.0,
                    no: else_val.0,
                }
            }
            // The check's kind (trust-ir v52) names WHICH panic a failure is,
            // not whether it fails: the model's outcome is the bare panic. So
            // the family admits exactly the kind of this program's one check,
            // the u16 add overflow, and `Unspecified` (the decode of a pre-v52
            // assert, the same check unnamed); any other kind is a different
            // check. A SITED assert (v54) calls an entry the model does not
            // have, so it is outside the family.
            (
                Inst::Assert {
                    cond,
                    kind: AssertKind::Overflow(AssertOverflowOp::Add) | AssertKind::Unspecified,
                    site: None,
                },
                [],
            ) => Instruction::Assert(cond.0),
            (Inst::Return { values }, []) if values.len() == 1 => Instruction::Return(values[0].0),
            _ => {
                return Err(
                    "unsupported actual scalar instruction/result shape; nothing omitted".into()
                );
            }
        };
        code.push(instruction);
    }
    if code != fixed_program() {
        return Err(
            "actual instruction/operand/value census is outside fixed successor family".into()
        );
    }
    Ok(code)
}

fn fixed_program() -> Vec<Instruction> {
    vec![
        Instruction::Widen { result: 1, operand: 0 },
        Instruction::U16 { result: 2, value: 1 },
        Instruction::AddOverflow { result: 3, flag: 4, left: 1, right: 2 },
        Instruction::Bool { result: 5, value: false },
        Instruction::Bool { result: 6, value: true },
        Instruction::Select { result: 7, condition: 4, yes: 5, no: 6 },
        Instruction::Assert(7),
        Instruction::Return(3),
    ]
}
