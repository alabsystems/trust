//! Exact native unsigned questions checked against the existing SemR Plan.
//! These are explicitly authored calculus inputs, not compiler captures.
use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort};
use trust_ir::{Block, BlockId, ProofDigest, ProofFormula};

use super::*;

#[derive(Clone, Copy, Debug)]
enum Shape {
    Select,
    Branch,
    Internal,
}

fn question(ty: Ty, shape: Shape) -> NativeVerificationBundle {
    use trust_wp_vc::contract_parser::parse_contract;
    let original = captured(false);
    let mut bundle = original.clone();
    let width = match ty {
        Ty::U8 => 8,
        Ty::U32 => 32,
        Ty::U64 => 64,
        _ => panic!("unsupported unsigned question"),
    };
    let mut formula = if matches!(shape, Shape::Internal) {
        // Preserve the authored text: never silently turn this question into
        // a reprinted JSON predicate in the checked consumer.
        ProofFormula::new("trust-wp.pure-expr.v1", "(r : bool) == (c : bool)")
    } else {
        let expression = parse_contract(
            "((c : bool) ==> ((r : Int) == (x : Int))) && (!(c : bool) ==> ((r : Int) == (y : Int)))",
        )
        .unwrap();
        // The existing typed serializer is the single native claim encoder.
        // This becomes this explicit question's original contract bytes.
        let claim = trust_wp_lib::trust_ir_body::scalar_claim(&expression).unwrap();
        ProofFormula::new("trust-wp.trust-formula.v1", claim.payload)
    };
    formula.bindings = vec![(
        "c".into(),
        ClauseBinding { sort: ClauseSort::Bool, place: ClausePlace::Param { index: 0 } },
    )];
    if !matches!(shape, Shape::Internal) {
        for (name, index) in [("x", 1), ("y", 2)] {
            formula.bindings.push((
                name.into(),
                ClauseBinding {
                    sort: ClauseSort::BitVec(width),
                    place: ClausePlace::Param { index },
                },
            ));
        }
    }
    formula.bindings.push((
        "r".into(),
        ClauseBinding {
            sort: if matches!(shape, Shape::Internal) {
                ClauseSort::Bool
            } else {
                ClauseSort::BitVec(width)
            },
            place: ClausePlace::ResultSlot { index: 0 },
        },
    ));
    let semantic_digest = ProofDigest::sha256_domain(
        "trust.root.explicit-unsigned-calculus.contract.v1",
        formula.payload.as_bytes(),
    );
    let obligation = &mut bundle.module.proof_obligations[0];
    obligation.formula = Some(formula);
    obligation.description = "explicit unsigned shared-IR calculus postcondition".into();
    let source = obligation.source.as_mut().unwrap();
    source.source_id = format!("explicit-calculus:unsigned-{width}:{shape:?}");
    source.public.as_mut().unwrap().semantic_digest = semantic_digest;
    let mut entry = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::Bool);
    let blocks = match shape {
        Shape::Select => {
            entry.params.extend([(ValueId::new(1), ty.clone()), (ValueId::new(2), ty.clone())]);
            entry.body = vec![
                InstrNode::new(Inst::Select {
                    ty: ty.clone(),
                    cond: ValueId::new(0),
                    then_val: ValueId::new(1),
                    else_val: ValueId::new(2),
                })
                .with_result(ValueId::new(3)),
                InstrNode::new(Inst::Return { values: vec![ValueId::new(3)] }),
            ];
            vec![entry]
        }
        Shape::Branch => {
            entry.params.extend([(ValueId::new(1), ty.clone()), (ValueId::new(2), ty.clone())]);
            // Both arms transfer to the same typed join. The predecessor
            // reads and simultaneous parameter binding remain canonical SemR.
            entry.body.push(InstrNode::new(Inst::CondBr {
                cond: ValueId::new(0),
                then_target: BlockId::new(1),
                then_args: vec![ValueId::new(1)],
                else_target: BlockId::new(1),
                else_args: vec![ValueId::new(2)],
            }));
            let mut join = Block::new(BlockId::new(1)).with_param(ValueId::new(3), ty.clone());
            join.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(3)] }));
            vec![entry, join]
        }
        Shape::Internal => {
            let maximum = match ty {
                Ty::U8 => i128::from(u8::MAX),
                Ty::U32 => i128::from(u32::MAX),
                Ty::U64 => i128::from(u64::MAX),
                _ => unreachable!(),
            };
            entry.params.extend([(ValueId::new(1), Ty::Bool), (ValueId::new(2), Ty::Bool)]);
            entry.body = vec![
                InstrNode::new(Inst::Const { ty: ty.clone(), value: Constant::Int(0) })
                    .with_result(ValueId::new(3)),
                InstrNode::new(Inst::Const { ty: ty.clone(), value: Constant::Int(maximum) })
                    .with_result(ValueId::new(4)),
                InstrNode::new(Inst::Select {
                    ty: ty.clone(),
                    cond: ValueId::new(0),
                    then_val: ValueId::new(3),
                    else_val: ValueId::new(4),
                })
                .with_result(ValueId::new(5)),
                InstrNode::new(Inst::ICmp {
                    ty: ty.clone(),
                    op: ICmpOp::Eq,
                    lhs: ValueId::new(5),
                    rhs: ValueId::new(3),
                })
                .with_result(ValueId::new(6)),
                InstrNode::new(Inst::Return { values: vec![ValueId::new(6)] }),
            ];
            vec![entry]
        }
    };
    let signature = &mut bundle.module.func_types[0];
    signature.params = if matches!(shape, Shape::Internal) {
        vec![Ty::Bool, Ty::Bool, Ty::Bool]
    } else {
        vec![Ty::Bool, ty.clone(), ty.clone()]
    };
    signature.returns = vec![if matches!(shape, Shape::Internal) { Ty::Bool } else { ty }];
    bundle.module.functions[0].blocks = blocks;
    refresh(&mut bundle);
    bundle.validate().unwrap();
    assert!(trust_ir_build::validate_module(&bundle.module).is_empty());
    assert_eq!(captured(false), original, "the retained capture is never changed");
    bundle
}

fn wrong_body(bundle: &NativeVerificationBundle, shape: Shape) -> NativeVerificationBundle {
    let mut changed = bundle.clone();
    let index = if matches!(shape, Shape::Internal) { 2 } else { 0 };
    match &mut changed.module.functions[0].blocks[0].body[index].inst {
        Inst::Select { then_val, else_val, .. } => std::mem::swap(then_val, else_val),
        Inst::CondBr { then_args, else_args, .. } => std::mem::swap(then_args, else_args),
        _ => panic!("the explicit program has one selected operation"),
    }
    refresh(&mut changed);
    changed.validate().unwrap();
    assert!(trust_ir_build::validate_module(&changed.module).is_empty());
    changed
}

fn wrong_contract(bundle: &NativeVerificationBundle) -> NativeVerificationBundle {
    let mut changed = bundle.clone();
    let formula = changed.module.proof_obligations[0].formula.as_mut().unwrap();
    if formula.schema == "trust-wp.pure-expr.v1" {
        formula.payload = format!("!({})", formula.payload);
    } else {
        let mut payload: serde_json::Value = serde_json::from_str(&formula.payload).unwrap();
        payload["body"] = serde_json::json!({"op":"not", "expr":payload["body"].clone()});
        formula.payload = payload.to_string();
    }
    refresh(&mut changed);
    changed.validate().unwrap();
    assert!(trust_ir_build::validate_module(&changed.module).is_empty());
    changed
}

fn wrong_bindings(bundle: &NativeVerificationBundle, shape: Shape) -> NativeVerificationBundle {
    let mut changed = bundle.clone();
    for (name, binding) in
        &mut changed.module.proof_obligations[0].formula.as_mut().unwrap().bindings
    {
        binding.place = match (shape, name.as_str(), binding.place) {
            (Shape::Internal, "c", _) => ClausePlace::Param { index: 1 },
            (_, "x", ClausePlace::Param { index: 1 }) => ClausePlace::Param { index: 2 },
            (_, "y", ClausePlace::Param { index: 2 }) => ClausePlace::Param { index: 1 },
            _ => binding.place,
        };
    }
    refresh(&mut changed);
    changed.validate().unwrap();
    assert!(trust_ir_build::validate_module(&changed.module).is_empty());
    changed
}

fn wrong_width(
    bundle: &NativeVerificationBundle,
    ty: &Ty,
    shape: Shape,
) -> NativeVerificationBundle {
    let mut changed = bundle.clone();
    let index = if matches!(shape, Shape::Internal) { 0 } else { 1 };
    changed.module.proof_obligations[0].formula.as_mut().unwrap().bindings[index].1.sort =
        ClauseSort::BitVec(if *ty == Ty::U8 { 32 } else { 8 });
    refresh(&mut changed);
    changed
}

fn quoted_bindings(formula: &ProofFormula) -> String {
    formula
        .bindings
        .iter()
        .map(|(name, binding)| {
            let place = match binding.place {
                ClausePlace::Param { index } => format!(".param {index}"),
                ClausePlace::ResultSlot { index } => format!(".result {index}"),
                _ => panic!("unsupported explicit scalar place"),
            };
            let ty = match binding.sort {
                ClauseSort::Bool => ".bool",
                ClauseSort::BitVec(8) => ".int .u8",
                ClauseSort::BitVec(32) => ".int .u32",
                ClauseSort::BitVec(64) => ".int .u64",
                _ => panic!("unsupported explicit scalar binding type"),
            };
            format!("({}, {place}, {ty})", literal(name.bytes()))
        })
        .collect::<Vec<_>>()
        .join(",")
}

fn quoted_json(payload: &str) -> String {
    native_boolean_claim::json(
        &serde_json::from_str(payload).unwrap(),
        native_boolean_claim::layout(payload),
        0,
    )
    .unwrap()
}

fn identity(witness: &NativeBodyWpTranslationWitness) -> String {
    format!(
        "{{ bundleDigest := {}, moduleDigest := {}, requestDigest := {}, bodyDigest := {}, requestId := {}, functionId := {}, obligations := [{}], contractBytes := {}, questionBytes := {} }}",
        literal(witness.native_bundle_digest.bytes),
        literal(witness.module_digest.bytes),
        literal(witness.native_request_digest.bytes),
        literal(witness.function_body_digest.bytes),
        witness.request.index(),
        witness.function.index(),
        witness
            .contracts
            .iter()
            .map(|(id, _)| id.index().to_string())
            .collect::<Vec<_>>()
            .join(","),
        literal(witness.contracts[0].1.payload.bytes()),
        literal(witness.derived_request.obligations[0].claim.payload.bytes()),
    )
}

fn artifact(
    bundle: &NativeVerificationBundle,
    ty: &Ty,
    shape: Shape,
    scratch: &Path,
    family: &Path,
    module_name: &str,
) {
    let original = bundle.clone();
    let bytes = trust_ir::binary::serialize_module(&bundle.module).unwrap();
    assert_eq!(trust_ir::binary::deserialize_module(&bytes).unwrap(), bundle.module);
    std::fs::write(scratch.join("original.tirb"), &bytes).unwrap();
    let witnesses = trust_ir_native_bundle_to_body_translation_witnesses(bundle).unwrap();
    assert_eq!(witnesses.len(), 1);
    let witness = &witnesses[0];
    for (name, value) in [
        ("original-native.json", serde_json::to_vec_pretty(bundle).unwrap()),
        ("witness.json", serde_json::to_vec_pretty(witness).unwrap()),
    ] {
        std::fs::write(scratch.join(name), value).unwrap();
    }
    assert_eq!(witness.coverage, NativeBodyWpTranslationCoverage::UnsignedAssignmentCfg);
    replay_trust_ir_body_translation_witnesses(bundle, &witnesses).unwrap();
    let results = verify_trust_ir_body_contracts(bundle).unwrap();
    std::fs::write(
        scratch.join("fresh-results.json"),
        serde_json::to_vec_pretty(&results).unwrap(),
    )
    .unwrap();
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].status, trust_wp_lib::VerifyBundleStatus::Verified, "{results:#?}");
    replay_trust_ir_body_contracts(bundle, &results).unwrap();
    assert_eq!(witness.contracts.len(), 1);
    let formula = &witness.contracts[0].1;
    let post = original_contract_predicate(formula);
    let vc =
        native_predicate_for_obligation(&witness.derived_request.obligations[0]).unwrap().predicate;
    assert_eq!(
        post.free_vars().into_iter().collect::<BTreeSet<_>>(),
        formula.bindings.iter().map(|(name, _)| name.clone()).collect()
    );
    let changed_body = wrong_body(bundle, shape);
    let changed_contract = wrong_contract(bundle);
    let changed_bindings = wrong_bindings(bundle, shape);
    let changed_width = wrong_width(bundle, ty, shape);
    for (name, changed) in [
        ("body", &changed_body),
        ("contract", &changed_contract),
        ("bindings", &changed_bindings),
        ("width", &changed_width),
    ] {
        std::fs::write(
            scratch.join(format!("mutated-{name}-native.json")),
            serde_json::to_vec_pretty(changed).unwrap(),
        )
        .unwrap();
    }
    for (name, changed) in
        [("body", &changed_body), ("contract", &changed_contract), ("bindings", &changed_bindings)]
    {
        let refused = verify_trust_ir_body_contracts(changed).unwrap();
        std::fs::write(
            scratch.join(format!("mutated-{name}-results.json")),
            serde_json::to_vec_pretty(&refused).unwrap(),
        )
        .unwrap();
        assert_eq!(refused.len(), 1, "changed {name} must retain its obligation");
        assert_eq!(
            refused[0].status,
            trust_wp_lib::VerifyBundleStatus::Failed,
            "changed {name} must establish the false original contract: {refused:#?}"
        );
        assert!(replay_trust_ir_body_contracts(changed, &results).is_err());
        assert!(replay_trust_ir_body_translation_witnesses(changed, &witnesses).is_err());
    }
    let changed_formula = changed_contract.module.proof_obligations[0].formula.as_ref().unwrap();
    let changed_post = original_contract_predicate(changed_formula);
    let mut changed_vc = witness.clone();
    changed_vc.derived_request.obligations[0].claim = trust_wp_lib::BundleClaim::new(
        trust_wp_lib::BundleClaimFormat::TrustFormulaV1,
        r#"{"schema":"trust-wp.trust-formula.v1","variables":[],"body":{"bool":false}}"#,
    );
    assert!(changed_vc.derived_request.validation_diagnostics().is_empty());
    assert!(
        replay_trust_ir_body_translation_witnesses(bundle, std::slice::from_ref(&changed_vc))
            .is_err()
    );
    assert!(
        trust_wp_lib::replay_verify_bundle_result_evidence(
            &changed_vc.derived_request,
            &results[0]
        )
        .is_err()
    );
    let changed_vc_predicate =
        native_predicate_for_obligation(&changed_vc.derived_request.obligations[0])
            .unwrap()
            .predicate;
    for field in 0..4 {
        let mut changed = witness.clone();
        match field {
            0 => changed.parameters[0].1.push_str("_changed"),
            1 => changed.module_digest.bytes[0] ^= 1,
            2 => changed.native_bundle_digest.bytes[0] ^= 1,
            3 => changed.native_request_digest.bytes[0] ^= 1,
            _ => unreachable!(),
        }
        assert!(replay_trust_ir_body_translation_witnesses(bundle, &[changed]).is_err());
    }
    let mut changed_source = bundle.clone();
    changed_source.module.proof_obligations[0]
        .source
        .as_mut()
        .unwrap()
        .source_id
        .push_str(":changed");
    refresh(&mut changed_source);
    changed_source.validate().unwrap();
    assert!(replay_trust_ir_body_contracts(&changed_source, &results).is_err());
    assert!(replay_trust_ir_body_translation_witnesses(&changed_source, &witnesses).is_err());
    std::fs::write(
        scratch.join("mutated-source-native.json"),
        serde_json::to_vec_pretty(&changed_source).unwrap(),
    )
    .unwrap();
    assert!(replay_trust_ir_body_contracts(&changed_width, &results).is_err());
    assert!(replay_trust_ir_body_translation_witnesses(&changed_width, &witnesses).is_err());
    let function = &bundle.module.functions[0];
    let signature = &bundle.module.func_types[function.ty.index() as usize];
    let entry_index = function.blocks.iter().position(|block| block.id == function.entry).unwrap();
    let entry = &function.blocks[entry_index];
    assert_eq!(witness.parameters.len(), entry.params.len());
    let internal = matches!(shape, Shape::Internal);
    let variables = vec!["c", "x", "y"];
    let declaration = if internal { "(c x y : Bool)" } else { "(c : Bool) (x y : UInt)" };
    let arguments = variables.join(" ");
    let returned = if internal { "Bool" } else { "UInt" };
    let t = unsigned_type(ty).unwrap();
    let value = |name: &str, ty: &Ty| {
        if *ty == Ty::Bool { format!(".bool {name}") } else { format!(".int .{t} {name}.val") }
    };
    let inputs = signature
        .params
        .iter()
        .zip(&variables)
        .map(|(ty, name)| value(name, ty))
        .collect::<Vec<_>>()
        .join(",");
    let result = value("r", &signature.returns[0]);
    let environment = entry
        .params
        .iter()
        .zip(&variables)
        .rev()
        .map(|((id, ty), name)| format!("({}, {})", id.index(), value(name, ty)))
        .collect::<Vec<_>>()
        .join(",");
    let mut entry_booleans = Vec::new();
    let mut entry_integers = Vec::new();
    let entry_bindings = witness
        .parameters
        .iter()
        .zip(&entry.params)
        .zip(&variables)
        .map(|(((id, name), (expected, ty)), var)| {
            assert_eq!(id, expected);
            if *ty == Ty::Bool {
                entry_booleans.push(format!("({}, {var})", literal(name.bytes())));
            } else {
                entry_integers.push(format!("({}, Int.ofNat {var}.val)", literal(name.bytes())));
            }
            format!("({}, {}, {})", id.index(), literal(name.bytes()), type_literal(ty))
        })
        .collect::<Vec<_>>()
        .join(",");
    let mut post_booleans = Vec::new();
    let mut post_integers = Vec::new();
    let post_bindings = formula
        .bindings
        .iter()
        .map(|(name, binding)| {
            let (place, var, actual_ty) = match binding.place {
                ClausePlace::Param { index } => (
                    format!(".param {index}"),
                    variables[index as usize],
                    &signature.params[index as usize],
                ),
                ClausePlace::ResultSlot { index: 0 } => {
                    (".result 0".into(), "r", &signature.returns[0])
                }
                _ => panic!("unsupported explicit scalar contract place"),
            };
            let expected_sort = if *actual_ty == Ty::Bool {
                ClauseSort::Bool
            } else {
                ClauseSort::BitVec(match actual_ty {
                    Ty::U8 => 8,
                    Ty::U32 => 32,
                    Ty::U64 => 64,
                    _ => unreachable!(),
                })
            };
            assert_eq!(binding.sort, expected_sort);
            if *actual_ty == Ty::Bool {
                post_booleans.push(format!("({}, {var})", literal(name.bytes())));
            } else {
                post_integers.push(format!("({}, Int.ofNat {var}.val)", literal(name.bytes())));
            }
            format!("({}, {place}, {})", literal(name.bytes()), type_literal(actual_ty))
        })
        .collect::<Vec<_>>()
        .join(",");
    let post_names = formula
        .bindings
        .iter()
        .map(|(name, _)| literal(name.bytes()))
        .collect::<Vec<_>>()
        .join(",");
    let post_expression = native_boolean_claim::expression(&post, 0).unwrap();
    let changed_post_expression = native_boolean_claim::expression(&changed_post, 0).unwrap();
    let post_codec = if internal {
        format!(
            "def postNames : List SemRBooleanClaim.Name := [{post_names}]\ntheorem post_decoded : SemRBooleanClaim.decodeText 4096 postNames postBytes = some postExpression := rfl\ntheorem changed_post_decoded : SemRBooleanClaim.decodeText 4096 postNames changedPostBytes = some changedPostExpression := rfl\n"
        )
    } else {
        format!(
            "def postJson : SemRBooleanClaim.Json := {}\ndef changedPostJson : SemRBooleanClaim.Json := {}\ntheorem post_encoded : SemRBooleanClaim.encodeJson 4096 postJson = some postBytes := rfl\ntheorem post_decoded : SemRBooleanClaim.decodeClaim 4096 postJson = some postExpression := rfl\ntheorem changed_post_encoded : SemRBooleanClaim.encodeJson 4096 changedPostJson = some changedPostBytes := rfl\ntheorem changed_post_decoded : SemRBooleanClaim.decodeClaim 4096 changedPostJson = some changedPostExpression := rfl\n",
            quoted_json(&formula.payload),
            quoted_json(&changed_formula.payload)
        )
    };
    let checked_post = if internal {
        "SemRBooleanClaim.checkedText 4096 postBytes postNames bindings.1"
    } else {
        "SemRBooleanClaim.checkedTypedJson 4096 postBytes postJson bindings"
    };
    let checked_changed_post = if internal {
        "SemRBooleanClaim.checkedText 4096 changedPostBytes postNames bindings.1"
    } else {
        "SemRBooleanClaim.checkedTypedJson 4096 changedPostBytes changedPostJson bindings"
    };
    let post_codec_simp = if internal {
        "SemRBooleanClaim.checkedText,post_decoded,changed_post_decoded"
    } else {
        "SemRBooleanClaim.checkedTypedJson,post_encoded,post_decoded,changed_post_encoded,changed_post_decoded"
    };
    let entry_bounds = if internal { "" } else { ",x.isLt,y.isLt" };
    let post_bounds = if internal { "" } else { ",x.isLt,y.isLt,r.isLt" };
    let original_relation = if internal {
        "r == c"
    } else {
        "((!c || (Int.ofNat r.val == Int.ofNat x.val)) && (c || (Int.ofNat r.val == Int.ofNat y.val)))"
    };
    let rebound_arguments = if internal { "x x y" } else { "c y x" };
    let rebound_relation = if internal {
        "r == x"
    } else {
        "((!c || (Int.ofNat r.val == Int.ofNat y.val)) && (c || (Int.ofNat r.val == Int.ofNat x.val)))"
    };
    let binding_simp = "SemRBooleanClaim.contractTypedEnv,SemRBooleanClaim.boundValue,SemRBooleanClaim.typedEnv,expectTy,Val.ty,Ty.beq,IntTy.signed,Module.pointerBits,ok_bind";
    let sample = if internal {
        "post true false false false = false ∧ post true false false true = true"
    } else {
        "post true ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨0,by decide⟩ = true ∧ post true ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨1,by decide⟩ = false"
    };
    let vc_payload = &witness.derived_request.obligations[0].claim.payload;
    let changed_vc_payload = &changed_vc.derived_request.obligations[0].claim.payload;
    let common = "SemRBooleanClaim.entryTypedEnv,SemRBooleanClaim.contractTypedEnv,SemRBooleanClaim.boundValue,SemRBooleanClaim.typedEnv,SemRBooleanClaim.evalTyped,SemRBooleanClaim.eval,SemRBooleanClaim.lookup,SemRBooleanClaim.IntExpr.eval,SemRBooleanClaim.IntBinary.apply,SemRBooleanClaim.IntComparison.apply,SemRBooleanClaim.Binary.apply,expectTy,Val.ty,Ty.beq,IntTy.signed,Module.pointerBits,ok_bind";
    let claim_eval = "SemRBooleanClaim.evalTyped,SemRBooleanClaim.eval,SemRBooleanClaim.lookup,SemRBooleanClaim.IntExpr.eval,SemRBooleanClaim.IntBinary.apply,SemRBooleanClaim.IntComparison.apply,SemRBooleanClaim.Binary.apply";
    let other = if *ty == Ty::U8 { "u32" } else { "u8" };
    let normalization = execution_normalization(
        declaration,
        witness.function.index(),
        &arguments,
        &format!("(inputValues {arguments})"),
        &format!("∃ r : {returned}, vs = [{result}] ∧ ({original_relation}) = true"),
        &format!("∃ r : {returned}, vs = [{result}] ∧ (!({original_relation})) = true"),
    );
    let source = format!(
        r#"import SemRBooleanClaimText
set_option maxRecDepth 32768
namespace {module_name}
open SemR SemRBooleanWP SemRBooleanWPComposition SemRBooleanWPBranches SemRNativeWPPlan
abbrev UInt := Fin (modulus (IntTy.{t}.bits 64))
def blob : List Nat := {blob}
def wrongBlob : List Nat := {wrong_blob}
def changedContractBlob : List Nat := {changed_contract_blob}
def model : SemR.Module := {model}
def wrongModel : SemR.Module := {wrong_model}
theorem decoded : SemR.decode blob = .ok model := rfl
theorem wrong_decoded : SemR.decode wrongBlob = .ok wrongModel := rfl
theorem changed_contract_decoded : SemR.decode changedContractBlob = .ok model := rfl
def identity : QuestionIdentity := {identity}
def plan : Plan := {plan}
def postBytes : SemRBooleanClaim.Bytes := {post_bytes}
def postExpression : SemRBooleanClaim.Expr := {post_expression}
def changedPostBytes : SemRBooleanClaim.Bytes := {changed_post_bytes}
def changedPostExpression : SemRBooleanClaim.Expr := {changed_post_expression}
{post_codec}
def vcBytes : SemRBooleanClaim.Bytes := {vc_bytes}
def vcJson : SemRBooleanClaim.Json := {vc_json}
def vcExpression : SemRBooleanClaim.Expr := {vc_expression}
def changedVCBytes : SemRBooleanClaim.Bytes := {changed_vc_bytes}
def changedVCJson : SemRBooleanClaim.Json := {changed_vc_json}
def changedVCExpression : SemRBooleanClaim.Expr := {changed_vc_expression}
theorem vc_encoded : SemRBooleanClaim.encodeJson 4096 vcJson = some vcBytes := rfl
theorem vc_decoded : SemRBooleanClaim.decodeClaim 4096 vcJson = some vcExpression := rfl
theorem changed_vc_encoded : SemRBooleanClaim.encodeJson 4096 changedVCJson = some changedVCBytes := rfl
theorem changed_vc_decoded : SemRBooleanClaim.decodeClaim 4096 changedVCJson = some changedVCExpression := rfl
def entryBindings : List SemRBooleanClaim.EntryBinding := [{entry_bindings}]
def postBindings : List SemRBooleanClaim.ContractBinding := [{post_bindings}]
def wrongPostBindings : List SemRBooleanClaim.ContractBinding := [{wrong_post_bindings}]
def wrongWidthPostBindings : List SemRBooleanClaim.ContractBinding := [{wrong_width_post_bindings}]
def inputValues {declaration} : List Val := [{inputs}]
def initial {declaration} (depth : Nat) : Core :=
  {{ fn := model.functions[0], sig := model.funcTys[{signature}], block := model.functions[0].blocks[{entry_index}], pc := 0,
     env := [{environment}], depth := depth, stack := [], openFrames := [], nextFrame := 0, mem := Mem.empty }}
theorem entry_environment {declaration} : SemRBooleanClaim.entryTypedEnv model entryBindings (initial {arguments} 0) = some ([{entry_booleans}], [{entry_integers}]) := by
  simp [entryBindings,initial,model,lookupEnv,{common}{entry_bounds}] <;> decide
theorem contract_environment {declaration} (r : {returned}) : SemRBooleanClaim.contractTypedEnv model postBindings (inputValues {arguments}) [{result}] = some ([{post_booleans}], [{post_integers}]) := by
  simp [postBindings,inputValues,model,{common}{post_bounds}] <;> decide
def post {declaration} (r : {returned}) : Bool := (do
  let bindings ← SemRBooleanClaim.contractTypedEnv model postBindings (inputValues {arguments}) [{result}]
  {checked_post}).getD false
def changedPost {declaration} (r : {returned}) : Bool := (do
  let bindings ← SemRBooleanClaim.contractTypedEnv model postBindings (inputValues {arguments}) [{result}]
  {checked_changed_post}).getD false
def reboundPost {declaration} (r : {returned}) : Bool := (do
  let bindings ← SemRBooleanClaim.contractTypedEnv model wrongPostBindings (inputValues {arguments}) [{result}]
  {checked_post}).getD false
def wrongWidthPost {declaration} (r : {returned}) : Bool := (do
  let bindings ← SemRBooleanClaim.contractTypedEnv model wrongWidthPostBindings (inputValues {arguments}) [{result}]
  {checked_post}).getD false
def vc {declaration} : Bool := (do
  let bindings ← SemRBooleanClaim.entryTypedEnv model entryBindings (initial {arguments} 0)
  SemRBooleanClaim.checkedTypedJson 4096 vcBytes vcJson bindings).getD false
def changedVC {declaration} : Bool := (do
  let bindings ← SemRBooleanClaim.entryTypedEnv model entryBindings (initial {arguments} 0)
  SemRBooleanClaim.checkedTypedJson 4096 changedVCBytes changedVCJson bindings).getD false
def holds {declaration} (vs : List Val) : Prop := ∃ r : {returned}, vs = [{result}] ∧ post {arguments} r = true
theorem original_postcondition {declaration} (r : {returned}) : post {arguments} r = ({original_relation}) := by
  cases c <;> simp [post,contract_environment,{post_codec_simp},postExpression,{claim_eval}]
theorem contract_nontrivial : {sample} := by simp [original_postcondition]
theorem starts {declaration} (depth : Nat) : start model {fid} (inputValues {arguments}) depth = .ok (initial {arguments} depth) := by
  simp [start,model,initial,inputValues,checkSig,findBlock,nth?,bindParams,Module.executableTarget,rejectPoison,{common}{entry_bounds}] <;> rfl
theorem vc_to_wp {declaration} (depth : Nat) (_hvc : vc {arguments} = true) : wp model (holds {arguments}) plan (initial {arguments} depth) := by
  cases c <;> simp [wp,plan,model,initial,holds,original_postcondition,scalarWPWithUInt,scalarWP,
    SemRUnsignedSelect.selectUIntWP,SemRUnsignedSelect.copyUIntWP,SemRUnsignedSelect.constUIntWP,
    SemRUnsignedSelect.returnUIntWP,SemRUnsignedSelect.icmpEqUIntWP,SemRUnsignedSelect.writeUInt,
    SemRUnsignedSelect.writeBoolResult,SemRUnsignedSelect.selectUInt,SemRUnsignedSelect.copyUInt,
    SemRUnsignedSelect.constUInt,SemRUnsignedSelect.returnUInt,SemRUnsignedSelect.icmpEqUInt,
    SemRBooleanWPComposition.returnUIntWP,conditionalWP,jumpWP,argsWP,returnWP,
    constWP,copyWP,selectWP,writeBool,next,getV,lookupEnv,nth?,returnNode,
    constNode,copyNode,selectNode,branchNode,conditionalNode,findBlock,bindParams,{common},Fin.val_inj,modulus,IntTy.bits{entry_bounds}] <;> exact ⟨_, rfl, rfl⟩
theorem vc_valid {declaration} : vc {arguments} = true := by
  cases c <;> simp [vc,entry_environment,SemRBooleanClaim.checkedTypedJson,vc_encoded,vc_decoded,vcExpression,{claim_eval}]
theorem changed_postcondition {declaration} (r : {returned}) : changedPost {arguments} r = !(post {arguments} r) := by
  cases c <;> simp [changedPost,post,contract_environment,{post_codec_simp},postExpression,changedPostExpression,{claim_eval}]
theorem changed_vc_false {declaration} : changedVC {arguments} = false := by
  simp [changedVC,entry_environment,SemRBooleanClaim.checkedTypedJson,changed_vc_encoded,changed_vc_decoded,changedVCExpression,{claim_eval}]
def ExecutionClaim : Prop := ∀ {declaration} (depth : Nat), ∃ fuel vs,
  runBlob blob {fid} (inputValues {arguments}) fuel depth = .ok (.ret vs) ∧ holds {arguments} vs
theorem execution : ExecutionClaim := by
  intro {arguments} depth
  obtain ⟨fuel,vs,hr,hp⟩ := wp_run model (holds {arguments}) plan (initial {arguments} depth) (vc_to_wp {arguments} depth (vc_valid {arguments}))
  refine ⟨fuel,vs,?_,hp⟩
  simp only [runBlob,decoded,runFunction,starts]
  exact congrArg Except.ok hr
theorem bound_execution : BoundTranslation identity ExecutionClaim := ⟨execution⟩
theorem no_body_violation {declaration} (depth : Nat) : ¬ BodyViolation model (initial {arguments} depth) :=
  wp_excludes_violation model (holds {arguments}) plan (initial {arguments} depth) (vc_to_wp {arguments} depth (vc_valid {arguments}))
def WrongBody : Prop := ∀ {declaration} (depth : Nat), ∃ fuel vs,
  runBlob wrongBlob {fid} (inputValues {arguments}) fuel depth = .ok (.ret vs) ∧ holds {arguments} vs
def WrongContract : Prop := ∀ {declaration} (depth : Nat), ∃ fuel vs,
  runBlob changedContractBlob {fid} (inputValues {arguments}) fuel depth = .ok (.ret vs) ∧ ∃ r : {returned}, vs = [{result}] ∧ changedPost {arguments} r = true
def WrongVC : Prop := ∀ {declaration}, changedVC {arguments} = true
def WrongIdentity : Prop := BoundTranslation {{ identity with requestId := identity.requestId + 1 }} ExecutionClaim
def WrongBindings : Prop := ∀ {declaration} (depth : Nat), ∃ fuel vs,
  runBlob blob {fid} (inputValues {arguments}) fuel depth = .ok (.ret vs) ∧ ∃ r : {returned}, vs = [{result}] ∧ reboundPost {arguments} r = true
def WrongWidth : Prop := ∀ {declaration} (depth : Nat), ∃ fuel vs,
  runBlob blob {fid} (inputValues {arguments}) fuel depth = .ok (.ret vs) ∧ ∃ r : {returned}, vs = [{result}] ∧ wrongWidthPost {arguments} r = true
theorem width_mismatch_refused : SemRBooleanClaim.boundValue 64 (.int .{other}) (.int .{t} 0) = none := rfl
theorem out_of_range_refused : SemRBooleanClaim.boundValue 64 (.int .{t}) (.int .{t} (modulus (IntTy.{t}.bits 64))) = none := rfl
theorem poison_binding_refused : SemRBooleanClaim.boundValue 64 (.int .{t}) (.poison (.int .{t})) = none := rfl
theorem duplicate_contract_binding_refused : SemRBooleanClaim.contractTypedEnv model [([120],.param 0,.bool),([120],.result 0,.bool)] [.bool true] [.bool false] = none := rfl
theorem missing_result_binding_refused : SemRBooleanClaim.contractTypedEnv model [([120],.result 1,.int .{t})] [] [.int .{t} 0] = none := rfl
theorem duplicate_entry_binding_refused : SemRBooleanClaim.entryTypedEnv model [(0,[120],.bool),(0,[121],.bool)] (initial {zero_arguments} 0) = none := rfl
theorem changed_vc_bytes_refused {declaration} : SemRBooleanClaim.checkedTypedJson 4096 (vcBytes ++ [32]) vcJson ([{entry_booleans}], [{entry_integers}]) = none := by
  simp only [SemRBooleanClaim.checkedTypedJson,vc_encoded]
  have different : vcBytes ≠ vcBytes ++ [32] := by decide
  simp [different]
{normalization}
theorem rebound_postcondition {declaration} (r : {returned}) : reboundPost {arguments} r = post {rebound_arguments} r := by
  simp [reboundPost,post,wrongPostBindings,postBindings,inputValues,model,{binding_simp}{post_bounds}]
theorem wrong_width_postcondition {declaration} (r : {returned}) : wrongWidthPost {arguments} r = false := by
  rfl
def ModelWrongBindings : Prop := ∀ {declaration} (depth : Nat), ∃ fuel vs,
  runFunction model {fid} (inputValues {arguments}) fuel depth = .ret vs ∧ ∃ r : {returned}, vs = [{result}] ∧ ({rebound_relation}) = true
def ModelWrongWidth : Prop := ∀ {declaration} (depth : Nat), ∃ fuel vs,
  runFunction model {fid} (inputValues {arguments}) fuel depth = .ret vs ∧ ∃ r : {returned}, vs = [{result}] ∧ (false : Bool) = true
theorem wrong_bindings_model_equiv : WrongBindings ↔ ModelWrongBindings := by
  simp only [WrongBindings, ModelWrongBindings, SemR.runBlob, decoded,
    Except.ok.injEq, rebound_postcondition, original_postcondition]
theorem wrong_width_model_equiv : WrongWidth ↔ ModelWrongWidth := by
  simp only [WrongWidth, ModelWrongWidth, SemR.runBlob, decoded,
    Except.ok.injEq, wrong_width_postcondition]
#print axioms wrong_bindings_model_equiv
#print axioms wrong_width_model_equiv
#print axioms bound_execution
#print axioms original_execution_roundtrip
#print axioms original_vc_roundtrip
end {module_name}
"#,
        blob = literal(bytes.iter().copied()),
        wrong_blob = literal(trust_ir::binary::serialize_module(&changed_body.module).unwrap()),
        changed_contract_blob =
            literal(trust_ir::binary::serialize_module(&changed_contract.module).unwrap()),
        model = module_literal(&bundle.module),
        wrong_model = module_literal(&changed_body.module),
        identity = identity(witness),
        plan = plan(&witness.plan, &signature.returns[0]),
        post_bytes = literal(formula.payload.bytes()),
        changed_post_bytes = literal(changed_formula.payload.bytes()),
        wrong_post_bindings =
            quoted_bindings(changed_bindings.module.proof_obligations[0].formula.as_ref().unwrap()),
        wrong_width_post_bindings =
            quoted_bindings(changed_width.module.proof_obligations[0].formula.as_ref().unwrap()),
        vc_bytes = literal(vc_payload.bytes()),
        vc_json = quoted_json(vc_payload),
        vc_expression = native_boolean_claim::expression(&vc, 0).unwrap(),
        changed_vc_bytes = literal(changed_vc_payload.bytes()),
        changed_vc_json = quoted_json(changed_vc_payload),
        changed_vc_expression = native_boolean_claim::expression(&changed_vc_predicate, 0).unwrap(),
        signature = function.ty.index(),
        fid = witness.function.index(),
        entry_booleans = entry_booleans.join(","),
        entry_integers = entry_integers.join(","),
        post_booleans = post_booleans.join(","),
        post_integers = post_integers.join(","),
        zero_arguments = if internal {
            "false false false"
        } else {
            "false ⟨0,by decide⟩ ⟨0,by decide⟩"
        },
    );
    for (name, value) in [(
        "mutated-vc-request.json",
        serde_json::to_vec_pretty(&changed_vc.derived_request).unwrap(),
    )] {
        std::fs::write(scratch.join(name), value).unwrap();
    }
    compile_lean(scratch, family, module_name, &source);
    assert_eq!(*bundle, original);
}

pub(super) fn artifacts(
    env: &mut Environment,
    targets: &mut BTreeSet<Name>,
    family: &Path,
) -> Vec<String> {
    let root = std::env::var_os("TRUST_NATIVE_WP_TRANSLATION_EVIDENCE_DIR")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| std::path::PathBuf::from(env!("CARGO_TARGET_TMPDIR")));
    std::fs::create_dir_all(&root).unwrap();
    let mut modules = Vec::new();
    for (ty, width) in [(Ty::U8, 8), (Ty::U32, 32), (Ty::U64, 64)] {
        let select = question(ty.clone(), Shape::Select);
        let branch = question(ty.clone(), Shape::Branch);
        assert_eq!(
            select.module.proof_obligations[0].formula, branch.module.proof_obligations[0].formula,
            "Select and branch retain the same original typed question"
        );
        for (shape, bundle) in [
            (Shape::Select, select),
            (Shape::Branch, branch),
            (Shape::Internal, question(ty.clone(), Shape::Internal)),
        ] {
            let original = bundle.clone();
            let module_name = format!("NativeWpU{width}{shape:?}");
            let scratch = tempfile::tempdir_in(&root).unwrap().keep();
            eprintln!("actual fresh unsigned translation artifact: {}", scratch.display());
            artifact(&bundle, &ty, shape, &scratch, family, &module_name);
            load_module_with_deps(
                env,
                &module_name,
                &[
                    scratch,
                    family.to_path_buf(),
                    clean_olean::require_pinned_lean_lib_path().unwrap(),
                ],
            )
            .unwrap();
            for short in [
                "decoded",
                "wrong_decoded",
                "ModelExecution",
                "ModelWrongBody",
                "ModelWrongContract",
                "execution_model_equiv",
                "wrong_body_model_equiv",
                "wrong_contract_model_equiv",
                "model_execution",
                "original_execution_roundtrip",
                "VCClaim",
                "ModelVC",
                "ModelWrongVC",
                "vc_model_equiv",
                "wrong_vc_model_equiv",
                "model_vc",
                "original_vc_roundtrip",
                "rebound_postcondition",
                "wrong_width_postcondition",
                "ModelWrongBindings",
                "ModelWrongWidth",
                "wrong_bindings_model_equiv",
                "wrong_width_model_equiv",
                "changed_contract_decoded",
                "post_decoded",
                "vc_encoded",
                "vc_decoded",
                "changed_post_decoded",
                "changed_vc_encoded",
                "changed_vc_decoded",
                "entry_environment",
                "contract_environment",
                "original_postcondition",
                "contract_nontrivial",
                "starts",
                "vc_to_wp",
                "vc_valid",
                "changed_postcondition",
                "changed_vc_false",
                "execution",
                "bound_execution",
                "no_body_violation",
                "WrongBody",
                "WrongContract",
                "WrongVC",
                "WrongIdentity",
                "WrongBindings",
                "WrongWidth",
                "width_mismatch_refused",
                "out_of_range_refused",
                "poison_binding_refused",
                "duplicate_contract_binding_refused",
                "missing_result_binding_refused",
                "duplicate_entry_binding_refused",
                "changed_vc_bytes_refused",
            ] {
                targets.insert(Name::from_string(&format!("{module_name}.{short}")));
            }
            if !matches!(shape, Shape::Internal) {
                for short in ["post_encoded", "changed_post_encoded"] {
                    targets.insert(Name::from_string(&format!("{module_name}.{short}")));
                }
            }
            modules.push(module_name);
            assert_eq!(bundle, original);
        }
    }
    modules
}
