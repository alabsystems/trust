//! Instruction definedness must reach the compiler-facing safety result.

use trust_ir::{BinOp, Constant, Inst, InstrNode, Ty, ValueId};

use super::*;

fn division_bundle(
    op: BinOp,
    divisor: i128,
) -> (TrustContractBundle, trust_ir::NativeVerificationBundle) {
    let mut public = compiler_style_panic_freedom_public_bundle();
    // This unit fixture attests the flat query only. As on the existing
    // refutation-scope tests, it grants no native source correspondence.
    attest_synthetic_typed_chc_encoding_exact(&mut public.obligations[0]);
    let mut native = compiler_style_safe_tmir_bundle();
    let function = &mut native.module.functions[0];
    let next = function
        .blocks
        .iter()
        .flat_map(|block| {
            block
                .params
                .iter()
                .map(|(value, _)| *value)
                .chain(block.body.iter().flat_map(|node| node.results.iter().copied()))
        })
        .map(ValueId::index)
        .max()
        .expect("the original fixture defines SSA values")
        + 1;
    let lhs = ValueId::new(next);
    let rhs = ValueId::new(next + 1);
    let result = ValueId::new(next + 2);
    let entry = function.block_mut(function.entry).expect("the original entry exists");
    // On the U8 carrier, SDiv/SRem interpret raw 128 and 255 as -128 and -1.
    // Their domain depends on the opcode, even when the result is unused.
    entry.body.splice(
        0..0,
        [
            InstrNode::new(Inst::Const { ty: Ty::U8, value: Constant::Int(128) }).with_result(lhs),
            InstrNode::new(Inst::Const { ty: Ty::U8, value: Constant::Int(divisor) })
                .with_result(rhs),
            InstrNode::new(Inst::BinOp { op, ty: Ty::U8, lhs, rhs }).with_result(result),
        ],
    );
    let errors = trust_ir_build::validate_module(&native.module);
    assert!(
        errors.is_empty(),
        "the original body plus unsigned-carrier division must be valid IR: {errors:#?}",
    );
    let native = bind_compiler_style_native_bundle_to_public(native, &public);
    (public, native)
}

fn solve_division(op: BinOp, divisor: i128) -> NativeTrustIrBundleEvidenceWithFreshReceipts {
    let (public, mut native) = division_bundle(op, divisor);
    // Model the existing live compiler issuer for this unit fixture, as the
    // whole-function receipt tests do. This is not an actual compiler capture.
    let source = trust_ir::SourceGenerationAuthority::mint_from_live_lowering(&mut native)
        .expect("valid unit fixture source authority");
    let adapter = TrustMcVerifierApiAdapter::new(
        TrustMcConfig::new().with_proof_mode(TrustMcProofMode::PdrIc3).with_timeout(10_000),
    );
    // Translation, solving and proof receipt production use the live entry.
    // No serialized solver result is accepted as proof authority.
    adapter
        .evidence_from_native_trust_ir_bundle_with_source_authority_and_deadline_and_fresh_receipts(
            &public,
            &public.obligations,
            &native,
            &source,
            None,
        )
}

#[test]
fn native_division_domain_cannot_mint_a_whole_function_safety_receipt() {
    for op in [BinOp::SDiv, BinOp::SRem] {
        for divisor in [255, 0] {
            let outcome = solve_division(op, divisor);
            assert_eq!(outcome.evidence.len(), 1, "{op:?}, {divisor}: {outcome:#?}");
            let evidence = &outcome.evidence[0];
            assert_eq!(
                evidence.status,
                EvidenceStatus::Unsupported,
                "undefined {op:?} must not prove panic freedom: {outcome:#?}",
            );
            assert!(evidence.proof_strength.is_none());
            assert!(evidence.counterexample.is_none(), "native source replay is still required");
            assert!(outcome.fresh_whole_function_receipts.is_empty());
            assert!(outcome.fresh_exact_direct_receipts.is_empty());
            assert!(
                evidence.diagnostics.iter().any(|text| {
                    text.contains("transport solved obligation")
                        && text.contains("without a proof:")
                        && text.contains("counterexample evidence is not a proof")
                }),
                "the real native query must be solved and rejected as non-proof counterexample evidence: {outcome:#?}",
            );
        }
    }
}

#[test]
fn native_division_domain_preserves_defined_whole_function_safety_proofs() {
    for (op, divisor) in
        [(BinOp::SDiv, 1), (BinOp::SRem, 1), (BinOp::UDiv, 255), (BinOp::URem, 255)]
    {
        let outcome = solve_division(op, divisor);
        assert_eq!(outcome.evidence.len(), 1, "{op:?}, {divisor}: {outcome:#?}");
        assert_eq!(
            outcome.evidence[0].status,
            EvidenceStatus::Proved,
            "defined {op:?} must preserve the real safety proof: {outcome:#?}",
        );
        assert_eq!(outcome.fresh_whole_function_receipts.len(), 1);
        assert!(outcome.fresh_exact_direct_receipts.is_empty());
    }
}
