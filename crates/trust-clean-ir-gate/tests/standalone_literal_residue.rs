// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Trust (WS5.20, `STANDALONE.p18_literal_out_of_range`): an out-of-range
//! numeral is emitted as its Lean residue (`(300 : UInt8)` IS 44), and the
//! residue is admitted ONLY because the Clean kernel decides the reflected
//! in-range literal definitionally equal to the untouched source numeral at the
//! exact carrier. A wrong residue is a kernel disagreement; the raw numeral is
//! not a spelling the reader accepts.

use clean_kernel::Name;
use trust_certify::lean_source_batch::{CheckedLeanSourceBatch, LeanSourceInput};
use trust_clean_ir_gate::standalone::admit_standalone_scalar;
use trust_clean_origin::CleanOriginShape;
use trust_clean_origin::emit::plan_standalone_clean_origin_body;
use trust_ir::value::{FuncId, FuncTyId};
use trust_ir::{Constant, Inst};

fn checked(source: &str) -> CheckedLeanSourceBatch {
    let batch = CheckedLeanSourceBatch::check(
        vec![LeanSourceInput {
            module: "Residues".to_owned(),
            path: "Residues.lean".to_owned(),
            source: source.to_owned(),
        }],
        false,
    );
    assert!(batch.accepted_context().is_some(), "{:?}", batch.errors());
    batch
}

#[test]
fn an_out_of_range_numeral_is_admitted_only_at_its_exact_residue() {
    let batch = checked(
        "def lit300 : UInt8 := 300\n\
         def wide (a : UInt64) : UInt16 := 65537\n",
    );
    let context = batch.accepted_context().unwrap();
    for (name, residue, raw) in [("lit300", 44_i128, 300_i128), ("wide", 1, 65537)] {
        let plan = plan_standalone_clean_origin_body(context.environment(), name).unwrap();
        assert!(matches!(plan.shape(), CleanOriginShape::ConstantUint { .. }), "{name}");
        let signature = trust_clean_ir::trust_ir_func_ty(plan.signature()).unwrap();
        let function = trust_clean_ir::emit_standalone_clean_origin_function(
            &plan,
            FuncId::new(0),
            FuncTyId::new(0),
        )
        .unwrap();
        let decl = Name::from_string(name);
        let emitted = function.blocks[0]
            .body
            .iter()
            .find_map(|node| match &node.inst {
                Inst::Const { value: Constant::Int(value), .. } => Some(*value),
                _ => None,
            })
            .expect("a literal body carries one Const");
        assert_eq!(emitted, residue, "{name}: the emitted literal is Lean's residue");
        admit_standalone_scalar(&context, &decl, &signature, &function)
            .unwrap_or_else(|refusal| panic!("{name}: {refusal}"));
        // Mutation: an off-by-one residue reaches the kernel and is refused.
        let mut wrong = function.clone();
        let mut raw_spelled = function.clone();
        for (mutant, value) in [(&mut wrong, residue + 1), (&mut raw_spelled, raw)] {
            for node in &mut mutant.blocks[0].body {
                if let Inst::Const { value: Constant::Int(v), .. } = &mut node.inst {
                    *v = value;
                }
            }
        }
        let stage = admit_standalone_scalar(&context, &decl, &signature, &wrong)
            .map(|_| ())
            .expect_err("a wrong residue must be refused")
            .stage();
        assert_eq!(stage, "kernel-disagreement", "{name}");
        // The raw out-of-range numeral is not an emitted spelling at all.
        let stage = admit_standalone_scalar(&context, &decl, &signature, &raw_spelled)
            .map(|_| ())
            .expect_err("an out-of-range Const is not a carrier value")
            .stage();
        assert_eq!(stage, "constant", "{name}");
    }
}
