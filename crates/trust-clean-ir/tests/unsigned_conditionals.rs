// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Execute the direct TrustIR producer against the unchanged source declaration's
//! kernel interpretation. These are pointwise execution checks; the separately
//! maintained independent reflector supplies symbolic correspondence tests.

use clean_kernel::{Environment, Expr, Name, TypeChecker};
use trust_certify::clean_island::{CleanIslandSession, unfold_island_application};
use trust_clean_ir::{emit_clean_origin_function, trust_ir_func_ty};
use trust_clean_origin::{CleanOriginShape, plan_clean_origin_body};
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::ty::Ty;
use trust_ir::value::{FuncId, FuncTyId};
use trust_ir::{Function, Inst, Module};

struct Prepared {
    env: Environment,
    function: Function,
    name: &'static str,
    carrier: String,
    ty: Ty,
}

impl Prepared {
    fn new(width: u32, name: &'static str, body: &str, params: &str, decisions: usize) -> Self {
        let carrier = format!("UInt{width}");
        let source = format!("def {name} ({params} : {carrier}) : {carrier} := {body}");
        let mut session = CleanIslandSession::new();
        let batch = session.check_all(&[source.as_str()]);
        assert!(!batch.is_rejected(), "source must kernel-check: {source}: {batch:?}");
        let env = session.environment().expect("untainted source environment").clone();
        let plan = plan_clean_origin_body(&env, name).expect("nested source must plan");
        assert!(matches!(plan.shape(), CleanOriginShape::UnsignedConditional { .. }));
        let signature = trust_ir_func_ty(plan.signature()).expect("exact unsigned signature");
        let ty = signature.returns[0].clone();
        assert_eq!(ty.bit_width(), Some(width));
        let function = emit_clean_origin_function(&plan, FuncId::new(0), FuncTyId::new(0))
            .expect("sealed unsigned source must emit");
        let mut module = Module::new(format!("unsigned-conditional::{name}::{width}"));
        module.func_types.push(signature);
        module.functions.push(function.clone());
        let failures = trust_ir_build::validate_module(&module);
        assert!(failures.is_empty(), "emitted module must validate: {failures:?}");
        assert_eq!(function.blocks.len(), 1);
        for select in [false, true] {
            let count = function.blocks[0]
                .body
                .iter()
                .filter(|node| {
                    if select {
                        matches!(&node.inst, Inst::Select { .. })
                    } else {
                        matches!(&node.inst, Inst::ICmp { .. })
                    }
                })
                .count();
            assert_eq!(count, decisions, "every source decision must be emitted");
        }
        assert!(function.summary.is_none() && function.proofs.is_empty());
        Self { env, function, name, carrier, ty }
    }

    fn numeral(&self, value: u128) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string(&format!("{}.ofNat", self.carrier)), vec![]),
            Expr::nat_lit(u64::try_from(value).expect("admitted unsigned value fits u64")),
        )
    }

    fn check(&self, args: &[u128]) -> u128 {
        let result = Interpreter::new()
            .execute_function(
                &self.function,
                args.iter().map(|&value| {
                    InterpretValue::int(self.ty.clone(), value as i128)
                        .expect("exact carrier input")
                }),
            )
            .expect("direct TrustIR must execute");
        assert_eq!(result.returns.len(), 1);
        let actual = result.returns[0].as_int().expect("unsigned result").as_unsigned();
        let source_args: Vec<_> = args.iter().map(|&value| self.numeral(value)).collect();
        let source = unfold_island_application(&self.env, self.name, &source_args)
            .expect("original source application must type-check and unfold");
        assert!(
            TypeChecker::new(&self.env).is_def_eq(&source, &self.numeral(actual)),
            "{} {:?} at {} disagrees with the kernel: {actual}",
            self.name,
            args,
            self.carrier,
        );
        actual
    }
}

#[test]
fn unsigned_conditionals_exhaust_both_uint8_classifiers() {
    let gpr =
        Prepared::new(8, "gpr", "if reg < 19 then 0 else if reg < 30 then 1 else 0", "reg", 2);
    let fpr = Prepared::new(8, "fpr", "if reg < 8 then 0 else if reg < 16 then 1 else 0", "reg", 2);
    for reg in 0..=255 {
        assert_eq!(gpr.check(&[reg]), u128::from((19..30).contains(&reg)));
        assert_eq!(fpr.check(&[reg]), u128::from((8..16).contains(&reg)));
    }
}

#[test]
fn unsigned_conditionals_keep_branching_parameters_and_all_carrier_widths() {
    for width in [8, 16, 32, 64] {
        let prepared = Prepared::new(
            width,
            "forked",
            "if a < b then (if b < 30 then a else b) else if a < 19 then b else a",
            "a b",
            3,
        );
        let max = (1u128 << width) - 1;
        for a in [0, 1, 18, 19, 20, 29, 30, 31, max >> 1, max] {
            for b in [0, 1, 18, 19, 20, 29, 30, 31, max >> 1, max] {
                prepared.check(&[a, b]);
            }
        }

        let literal_relations = Prepared::new(
            width,
            "literal_relations",
            "if a <= 10 then (if a = 7 then 1 else 2) else 3",
            "a",
            2,
        );
        for a in [0, 6, 7, 8, 10, 11, max] {
            let expected = if a <= 10 { if a == 7 { 1 } else { 2 } } else { 3 };
            assert_eq!(literal_relations.check(&[a]), expected);
        }
    }
}
