//! Untrusted wire tags cannot promote an independently reconstructed ABI row.

use super::*;
#[path = "../../tests/cer_common/mod.rs"]
mod cer_common;
use cer_common::*;

use crate::original_conjunction_certificate::{
    SubjectBinding, SymbolicContext, without_production,
};

fn input(fixture: &Fixture) -> CerInput<'_> {
    CerInput {
        m_cg: &fixture.m_cg,
        producers: &fixture.producers,
        bodies: &fixture.bodies,
        placements: &fixture.placements,
        object: &fixture.object,
        relocation_model: fixture.model,
    }
}

#[test]
fn malformed_formula_packet_cannot_promote_a_nonempty_abi_residue() {
    crate::verify_output_instantiate::on_route_stack(|| {
        let mut module = ModBuilder::new("formula_abi_negative");
        let signature = module.sig(&[trust_ir::Ty::U64], Some(trust_ir::Ty::U64));
        module.define("rung", signature, trust_ir::Linkage::External, |body| {
            let zero = body.konst(trust_ir::Ty::U64, 0);
            body.ret(zero);
        });
        let fixture =
            Fixture::new(module.finish(), DARWIN, trust_cg_codegen::pipeline::OptLevel::O3);
        let (offset, _) = function_words(&fixture.object, "rung")
            .into_iter()
            .find(|(_, word)| *word == 0xd2800000)
            .expect("the actual const-zero return materialization");
        // Replace the real mov x0,#0 with mov x19,#0. Source memory/calls stay
        // empty, while an actual callee-saved ABI equation is now false.
        let fixture = fixture.patched(|bytes| patch_word(bytes, offset, 0xd2800013));
        let baseline = fixture.report();
        let certificate = baseline.certificate("rung").unwrap();
        assert_eq!(certificate.obligations.o0_abi.grade, Grade::Refuted, "{}", explain(&baseline));

        let original = vec![(
            Formula::BitVec { value: 0, width: 64 },
            Formula::BitVec { value: 0, width: 64 },
        )];
        let context = SymbolicContext {
            bits: Default::default(),
            memories: Default::default(),
            sorts: Default::default(),
            exact_byte_arrays: true,
        };
        let goal =
            trust_ir::proof::encode_clean_expr_dag_v2(&clean_kernel::Expr::const_str("Bool"))
                .unwrap();
        let proof =
            trust_ir::proof::encode_clean_expr_dag_v2(&clean_kernel::Expr::const_str("Bool.true"))
                .unwrap();
        let digest = |bytes: &[u8]| hex(&Sha256::digest(bytes));
        // Deliberately malformed proof DATA, never a checked constructor or
        // retagged authority. Shape and subject binding are valid; the retained
        // original is not the fresh return+ABI conjunction and has no auxiliary
        // precondition proof. It must reach replay and fail without a producer.
        let packet = serde_json::json!({
            "model":4,
            "original":original,
            "original_sha256":digest(&serde_json::to_vec(&original).unwrap()),
            "context":context,
            "context_sha256":digest(&serde_json::to_vec(&context).unwrap()),
            "terms":{"clean_expr_dag_v2":{"goal":goal,"proof":proof}},
            "goal_sha256":digest(&goal),
            "proof_sha256":digest(&proof),
            "environment_sha256":"0".repeat(64),
            "environment_mode":"LeanReplay",
            "environment_recipe":"trust-ir.formula-v2-original-bytes+checked-source-goal+final-source-proof/v4",
            "kernel_version":clean_kernel::VERSION,
            "formula_evidence":{"cohort_sha256":"0".repeat(64),"foundations":[],"declarations":[0],"relation":[0]}
        });
        let mut wire: serde_json::Value = serde_json::from_str(&baseline.to_json()).unwrap();
        wire["certificates"][0]["original_proof"] = serde_json::json!({
            "subject":SubjectBinding::from_input(&input(&fixture), certificate).unwrap(),
            "packet":packet
        });
        let sidecar: OriginalReplaySidecar = serde_json::from_value(wire).unwrap();
        let packets =
            sidecar.certificates.into_iter().map(|row| (row.symbol.clone(), row)).collect();
        let (replayed, conjunctions) = step5_record::record(|| {
            without_production(|| {
                verify_compiled_module_inner(&input(&fixture), Some(&packets), None, false)
            })
        });
        let replayed = replayed.unwrap();
        let row = replayed.certificate("rung").unwrap();
        assert_eq!(
            conjunctions.len(),
            1,
            "the malformed packet must reach actual conjunction replay"
        );
        assert!(
            conjunctions[0].1.iter().any(|(left, right)| {
                let mut actual_abi = false;
                for term in [left, right] {
                    term.visit(&mut |term| {
                        actual_abi |=
                            matches!(term, Formula::Var(name, Sort::BitVec(64)) if name=="X19");
                    });
                }
                actual_abi
            }),
            "the independently reconstructed original must retain the nonempty x19 ABI equation"
        );
        assert_eq!(row.obligations.o0_abi.grade, Grade::Unknown, "{}", explain(&replayed));
        assert_eq!(row.obligations.o4_return.grade, Grade::Unknown, "{}", explain(&replayed));
        assert!(!row.is_kernel_proved());
        assert!(replayed.ships(crate::verify_output::EmitPolicy::StrictProvenOnly).is_err());
    });
}
