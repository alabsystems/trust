// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Kernel-replayed properties of exact, compiler-produced literal program semantics.
//!
//! This extends the literal refinement evidence with an authored theorem that may name
//! its exact `Program`, `Initial`, and EvalIR operations. It does not give an arbitrary
//! model authority over the program, authenticate the source compiler, or prove backend
//! equivalence. The caller chooses the property and must account for input coverage.

use clean_kernel::expr::Expr;
use clean_kernel::name::Name;
use clean_kernel::tc::TypeChecker;

use crate::clean_surface::{
    CLEAN_TEMPORAL_PRELUDE, checked_theorem, elaborate_suffix_with_parser_prelude,
};
use crate::literal_refinement::{
    LiteralInvocation, LiteralRefinementCertificate, LiteralRefinementError,
    LiteralRefinementTheorem, certify_literal_refinement, encode_expression, fresh_literal_context,
    recheck_literal_refinement, run_on_large_stack,
};

pub const LITERAL_PROPERTY_SCHEMA_V1: &str = "trust.literal-property/v1";

/// An exact literal invocation and a theorem checked in its isolated environment.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LiteralPropertyCertificate {
    pub schema: String,
    pub literal: LiteralRefinementCertificate,
    pub property_source: String,
    pub property: LiteralRefinementTheorem,
}

fn check(
    literal_source: String,
    property_source: String,
    theorem: String,
    stored: Option<LiteralRefinementTheorem>,
) -> Result<LiteralRefinementTheorem, LiteralRefinementError> {
    if property_source.len() > 32 * 1024 * 1024 {
        return Err(LiteralRefinementError::GeneratedSourceLimit {
            bytes: property_source.len(),
            maximum: 32 * 1024 * 1024,
        });
    }
    run_on_large_stack(move || {
        let (mut environment, mut context) = fresh_literal_context()?;
        elaborate_suffix_with_parser_prelude(
            &mut environment,
            &mut context,
            CLEAN_TEMPORAL_PRELUDE,
            &literal_source,
            "exact literal property input",
        )?;
        // An authored unit cannot replace earlier semantics through implemented_by/extern.
        // Parse it separately to EOF so an open namespace cannot capture generated input.
        context = context.fork_run();
        elaborate_suffix_with_parser_prelude(
            &mut environment,
            &mut context,
            CLEAN_TEMPORAL_PRELUDE,
            &property_source,
            "authored exact literal property",
        )?;
        let (theorem_type, proof_term) = checked_theorem(&environment, &theorem)?;
        let fresh = LiteralRefinementTheorem {
            theorem: theorem.clone(),
            theorem_type: encode_expression(theorem_type)?,
            proof_term: encode_expression(proof_term)?,
        };
        if let Some(stored) = stored {
            if stored != fresh {
                return Err(LiteralRefinementError::ArtifactMismatch {
                    theorem,
                    field: "literal property theorem or proof",
                });
            }
            let ty: Expr = serde_json::from_slice(&stored.theorem_type)
                .map_err(|e| LiteralRefinementError::MalformedArtifact(e.to_string()))?;
            let proof: Expr = serde_json::from_slice(&stored.proof_term)
                .map_err(|e| LiteralRefinementError::MalformedArtifact(e.to_string()))?;
            if environment.get_const(&Name::from_string(&stored.theorem)).is_none() {
                return Err(LiteralRefinementError::MalformedArtifact(
                    "literal property theorem is absent".into(),
                ));
            }
            TypeChecker::with_mode(&environment, environment.mode())
                .check_type(&proof, &ty)
                .map_err(|e| LiteralRefinementError::KernelRejected(e.to_string()))?;
        }
        Ok(fresh)
    })
}

/// Prove an authored property in the exact literal program's environment.
pub fn certify_literal_property(
    module_bytes: &[u8],
    function_id: u32,
    invocation: &LiteralInvocation,
    property_source: &str,
    theorem: &str,
) -> Result<LiteralPropertyCertificate, LiteralRefinementError> {
    let literal = certify_literal_refinement(module_bytes, function_id, invocation)?;
    let property =
        check(literal.clean_source.clone(), property_source.to_owned(), theorem.to_owned(), None)?;
    let certificate = LiteralPropertyCertificate {
        schema: LITERAL_PROPERTY_SCHEMA_V1.to_owned(),
        literal,
        property_source: property_source.to_owned(),
        property,
    };
    recheck_literal_property(
        &certificate,
        module_bytes,
        function_id,
        invocation,
        property_source,
        theorem,
    )?;
    Ok(certificate)
}

/// Rebuild the exact semantics and independently check the stored property term.
pub fn recheck_literal_property(
    certificate: &LiteralPropertyCertificate,
    module_bytes: &[u8],
    function_id: u32,
    invocation: &LiteralInvocation,
    property_source: &str,
    theorem: &str,
) -> Result<(), LiteralRefinementError> {
    if certificate.schema != LITERAL_PROPERTY_SCHEMA_V1 {
        return Err(LiteralRefinementError::SchemaMismatch { found: certificate.schema.clone() });
    }
    if certificate.property_source != property_source {
        return Err(LiteralRefinementError::SourceMismatch);
    }
    if certificate.property.theorem != theorem {
        return Err(LiteralRefinementError::TheoremSetMismatch);
    }
    recheck_literal_refinement(&certificate.literal, module_bytes, function_id, invocation)?;
    check(
        certificate.literal.clean_source.clone(),
        property_source.to_owned(),
        theorem.to_owned(),
        Some(certificate.property.clone()),
    )?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use trust_ir::{
        Block, BlockId, Constant, FuncId, FuncTy, FuncTyId, Function, Inst, InstrNode, Module, Ty,
        ValueId,
    };

    use super::*;

    // A codec fixture for the property API itself. The source-qualification driver
    // instead accepts only bytes actually emitted by the requested compiler.
    fn boolean_constant(value: bool) -> Vec<u8> {
        let mut module = Module::new("literal_property_api_fixture");
        module.func_types.push(FuncTy {
            params: vec![],
            returns: vec![Ty::Bool],
            is_vararg: false,
            abi: None,
        });
        let mut function =
            Function::new(FuncId::new(0), "answer", FuncTyId::new(0), BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(value) })
                .with_result(ValueId::new(0)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
        function.blocks.push(block);
        module.functions.push(function);
        trust_ir::binary::serialize_module(&module).unwrap()
    }

    const TRUE_RETURN: &str = "
theorem property_true :
  ir_run 8 Trust.LiteralRefinement.Program Trust.LiteralRefinement.Initial =
  IROutcome.ret (IRList.cons IRScalar (IRScalar.bool_ true) (IRList.nil IRScalar)) := rfl
";

    #[test]
    fn property_is_replayed_and_fresh_wrong_body_fails_semantically() {
        let invocation = LiteralInvocation::closed(vec![], 0);
        let good = boolean_constant(true);
        let bad = boolean_constant(false);
        let certificate =
            certify_literal_property(&good, 0, &invocation, TRUE_RETURN, "property_true").unwrap();
        let bytes = serde_json::to_vec(&certificate).unwrap();
        let restored = serde_json::from_slice(&bytes).unwrap();
        recheck_literal_property(&restored, &good, 0, &invocation, TRUE_RETURN, "property_true")
            .unwrap();
        assert!(matches!(
            recheck_literal_property(&restored, &bad, 0, &invocation, TRUE_RETURN, "property_true"),
            Err(LiteralRefinementError::ModuleMismatch)
        ));
        assert!(
            certify_literal_property(&bad, 0, &invocation, TRUE_RETURN, "property_true").is_err()
        );
        let false_return = TRUE_RETURN.replace("bool_ true", "bool_ false");
        certify_literal_property(&bad, 0, &invocation, &false_return, "property_true")
            .expect("the changed module is supported; only the old semantic claim fails");
    }
}
