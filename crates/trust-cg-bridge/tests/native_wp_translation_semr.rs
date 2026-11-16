//! Fresh native questions connected to the existing IR-owned SemR calculus.
//! These diagnostics grant neither source authority nor a solver proof grade.
//! Original Boolean text and structured VC bytes are checked in the kernel.
//! Rust proposes data, never a renamed logical predicate. Opaque identity
//! authentication and source refinement remain separate trusted boundaries.
use std::collections::BTreeSet;
use std::path::Path;
use std::process::Command;

use clean_kernel::ReferenceRefusal;
use clean_kernel::env::{Declaration, EnvError, Environment};
use clean_kernel::expr::Expr;
use clean_kernel::name::Name;
use clean_kernel::tc::TypeError;
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::{load_module_with_deps, reference_base_closed};
use sha2::{Digest, Sha256};
use trust_ir::{Constant, ICmpOp, Inst, InstrNode, NativeVerificationBundle, Ty, ValueId};
use trust_wp_lib::trust_ir_body::{
    NativeBodyWpProofPlan, NativeBodyWpTranslationCoverage, NativeBodyWpTranslationWitness,
    replay_trust_ir_body_contracts, replay_trust_ir_body_translation_witnesses,
    trust_ir_native_bundle_to_body_translation_witnesses, verify_trust_ir_body_contracts,
};
use trust_wp_vc::verify_bundle::native_predicate_for_obligation;

#[path = "../../../first-party/clean/crates/clean-olean/tests/support/native_boolean_claim.rs"]
mod native_boolean_claim;
#[path = "../../../first-party/clean/crates/clean-olean/tests/support/native_boolean_reaches.rs"]
mod native_boolean_reaches;

#[path = "native_wp_translation_semr/unsigned.rs"]
mod unsigned;

const CAPTURE: &[u8] = include_bytes!(
    "../../../first-party/clean/crates/clean-olean/tests/fixtures/native_wp/universal-permuted.json"
);

fn literal(bytes: impl IntoIterator<Item = u8>) -> String {
    native_boolean_claim::bytes(&bytes.into_iter().collect::<Vec<_>>())
}
fn values(values: &[ValueId]) -> String {
    format!("[{}]", values.iter().map(|v| v.index().to_string()).collect::<Vec<_>>().join(","))
}
fn original_contract_predicate(formula: &trust_ir::ProofFormula) -> trust_wp_vc::formula::PureExpr {
    // The body witness retains the original contract. Reuse its owning
    // codecs, without rebuilding a bodyless question that cannot admit
    // fixed-width bindings. The kernel checks the same original bytes.
    match formula.schema.as_str() {
        "trust-wp.trust-formula.v1" => {
            trust_wp_vc::verify_bundle::decode_trust_formula_v1_claim(&formula.payload)
                .expect("original typed scalar contract")
        }
        "trust-wp.pure-expr.v1" => trust_wp_vc::contract_parser::parse_contract(&formula.payload)
            .expect("original annotated Boolean contract"),
        other => panic!("untranslated original contract codec: {other}"),
    }
}
fn unsigned_type(ty: &Ty) -> Option<&'static str> {
    match ty {
        Ty::U8 => Some("u8"),
        Ty::U32 => Some("u32"),
        Ty::U64 => Some("u64"),
        _ => None,
    }
}
fn type_literal(ty: &Ty) -> String {
    if *ty == Ty::Bool {
        ".bool".into()
    } else if let Some(ty) = unsigned_type(ty) {
        format!(".int .{ty}")
    } else {
        panic!("untranslated type; no semantic fallback: {ty:?}")
    }
}
fn node(node: &InstrNode) -> String {
    assert!(node.proofs.is_empty());
    match (&node.inst, node.results.as_slice()) {
        (Inst::Const { ty: Ty::Bool, value: Constant::Bool(v) }, [dst]) => {
            format!("constNode {} {v}", dst.index())
        }
        (Inst::Copy { ty: Ty::Bool, operand }, [dst]) => {
            format!("copyNode {} {}", dst.index(), operand.index())
        }
        (Inst::Select { ty: Ty::Bool, cond, then_val, else_val }, [dst]) => format!(
            "selectNode {} {} {} {}",
            dst.index(),
            cond.index(),
            then_val.index(),
            else_val.index()
        ),
        (Inst::Const { ty, value: Constant::Int(value) }, [dst]) if unsigned_type(ty).is_some() => {
            // Quote the original wire pattern; the kernel's actual decode
            // equation checks its interpretation at the declared width.
            let pattern = u128::from_le_bytes(value.to_le_bytes());
            format!(
                "SemRUnsignedSelect.constUInt {} .{} {pattern}",
                dst.index(),
                unsigned_type(ty).unwrap()
            )
        }
        (Inst::Copy { ty, operand }, [dst]) if unsigned_type(ty).is_some() => format!(
            "SemRUnsignedSelect.copyUInt {} {} .{}",
            dst.index(),
            operand.index(),
            unsigned_type(ty).unwrap()
        ),
        (Inst::Select { ty, cond, then_val, else_val }, [dst]) if unsigned_type(ty).is_some() => {
            format!(
                "SemRUnsignedSelect.selectUInt {} {} {} {} .{}",
                dst.index(),
                cond.index(),
                then_val.index(),
                else_val.index(),
                unsigned_type(ty).unwrap()
            )
        }
        (Inst::ICmp { ty, op: ICmpOp::Eq, lhs, rhs }, [dst]) if unsigned_type(ty).is_some() => {
            format!(
                "SemRUnsignedSelect.icmpEqUInt {} {} {} .{}",
                dst.index(),
                lhs.index(),
                rhs.index(),
                unsigned_type(ty).unwrap()
            )
        }
        (Inst::Br { target, args }, []) => {
            format!("branchNode {} {}", target.index(), values(args))
        }
        (Inst::CondBr { cond, then_target, then_args, else_target, else_args }, []) => format!(
            "conditionalNode {} {} {} {} {}",
            cond.index(),
            then_target.index(),
            values(then_args),
            else_target.index(),
            values(else_args)
        ),
        (Inst::Return { values }, []) if values.len() == 1 => {
            format!("returnNode {}", values[0].index())
        }
        _ => panic!("untranslated node; no proof fragment fallback: {node:?}"),
    }
}
fn plan(witness: &NativeBodyWpProofPlan, returned: &Ty) -> String {
    let next = &witness.successors;
    match &witness.instruction.inst {
        Inst::Return { values } => {
            assert_eq!(values.len(), 1);
            assert!(next.is_empty());
            if *returned == Ty::Bool {
                format!(".returns {}", values[0].index())
            } else {
                format!(
                    ".returnsUInt {} .{}",
                    values[0].index(),
                    unsigned_type(returned).expect("untranslated result type")
                )
            }
        }
        Inst::Br { target, args } => {
            assert_eq!(next.len(), 1);
            format!(".jump {} {} ({})", target.index(), values(args), plan(&next[0], returned))
        }
        Inst::CondBr { cond, then_target, then_args, else_target, else_args } => {
            assert_eq!(next.len(), 2);
            format!(
                ".branch {} {} {} {} {} ({}) ({})",
                cond.index(),
                then_target.index(),
                values(then_args),
                else_target.index(),
                values(else_args),
                plan(&next[0], returned),
                plan(&next[1], returned)
            )
        }
        _ => {
            assert_eq!(next.len(), 1);
            format!(".scalar ({}) ({})", node(&witness.instruction), plan(&next[0], returned))
        }
    }
}

/// An untrusted typed literal emitter; the canonical decoder equation is
/// kernel-checked independently. This supplies no operational semantics.
fn module_literal(module: &trust_ir::Module) -> String {
    assert!(module.target_info.is_none());
    assert!(module.blobs.is_empty(), "tensor/blob tables have no scalar quotation");
    assert!(module.globals.is_empty() && module.imports.is_empty());
    assert!(module.structs.is_empty() && module.enums.is_empty());
    let types = module
        .func_types
        .iter()
        .map(|sig| {
            assert!(sig.abi.is_none() && !sig.is_vararg);
            let params = sig.params.iter().map(type_literal).collect::<Vec<_>>().join(",");
            let returns = sig.returns.iter().map(type_literal).collect::<Vec<_>>().join(",");
            format!("{{ params := [{params}], returns := [{returns}], vararg := false }}")
        })
        .collect::<Vec<_>>()
        .join(",");
    let functions = module
        .functions
        .iter()
        .map(|function| {
            let blocks = function
                .blocks
                .iter()
                .map(|block| {
                    let params = block
                        .params
                        .iter()
                        .map(|(id, ty)| format!("({}, {})", id.index(), type_literal(ty)))
                        .collect::<Vec<_>>()
                        .join(",");
                    let body = block
                        .body
                        .iter()
                        .map(|n| format!("({})", node(n)))
                        .collect::<Vec<_>>()
                        .join(",");
                    format!(
                        "{{ id := {}, params := [{params}], body := [{body}] }}",
                        block.id.index()
                    )
                })
                .collect::<Vec<_>>()
                .join(",");
            format!(
                "{{ id := {}, ty := {}, entry := {}, blocks := [{blocks}], name := {} }}",
                function.id.index(),
                function.ty.index(),
                function.entry.index(),
                literal(function.name.bytes())
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    format!("{{ funcTys := [{types}], enums := [], functions := [{functions}] }}")
}
fn refresh(bundle: &mut NativeVerificationBundle) {
    let digest = bundle.module.stable_digest();
    bundle.trust_ir_module_digest = digest;
    for row in &mut bundle.lineage.nodes {
        if bundle.lineage.roots.contains(&row.id) {
            row.target_module = digest;
        }
    }
}
fn captured(assignments: bool) -> NativeVerificationBundle {
    assert_eq!(
        format!("{:x}", Sha256::digest(CAPTURE)),
        "7b3b4641d71ef4b9cb935d1e2f9d724cca268945ad23e174228e8867fcb1cd9a"
    );
    let capture: serde_json::Value = serde_json::from_slice(CAPTURE).unwrap();
    let mut bundle: NativeVerificationBundle =
        serde_json::from_value(capture["bundle"].clone()).unwrap();
    bundle.validate().unwrap();
    if assignments {
        // A separate explicit calculus input, not a compiler/source claim.
        // The native question and its authored predicate stay unchanged.
        let body = &mut bundle.module.functions[0].blocks[1].body;
        body.insert(
            0,
            InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) })
                .with_result(ValueId::new(8)),
        );
        body.insert(
            1,
            InstrNode::new(Inst::Copy { ty: Ty::Bool, operand: ValueId::new(4) })
                .with_result(ValueId::new(9)),
        );
        body.insert(
            2,
            InstrNode::new(Inst::Select {
                ty: Ty::Bool,
                cond: ValueId::new(8),
                then_val: ValueId::new(9),
                else_val: ValueId::new(3),
            })
            .with_result(ValueId::new(10)),
        );
        let Inst::Br { args, .. } = &mut body[3].inst else { panic!("original branch") };
        *args = vec![ValueId::new(10)];
        refresh(&mut bundle);
    }
    bundle.validate().unwrap();
    assert!(trust_ir_build::validate_module(&bundle.module).is_empty());
    bundle
}

fn artifact(
    bundle: &NativeVerificationBundle,
    witness: &NativeBodyWpTranslationWitness,
    results: &[trust_wp_lib::VerifyBundleResult],
    scratch: &Path,
    family: &Path,
    module_name: &str,
) {
    assert_eq!(witness.coverage, NativeBodyWpTranslationCoverage::BooleanAssignmentCfg);
    replay_trust_ir_body_translation_witnesses(bundle, std::slice::from_ref(witness)).unwrap();
    assert_eq!(witness.contracts.len(), 1);
    let mut renamed_binding = witness.clone();
    renamed_binding.parameters[0].1.push_str("_changed");
    assert!(replay_trust_ir_body_translation_witnesses(bundle, &[renamed_binding]).is_err());
    let formula = &witness.contracts[0].1;
    let post = original_contract_predicate(formula);
    let vc =
        native_predicate_for_obligation(&witness.derived_request.obligations[0]).unwrap().predicate;
    let function = bundle.module.function_by_id(witness.function).unwrap();
    assert_eq!(bundle.module.functions.len(), 1);
    let entry_index = function.blocks.iter().position(|b| b.id == function.entry).unwrap();
    let entry = &function.blocks[entry_index];
    let parameters = (0..entry.params.len()).map(|i| format!("p{i}")).collect::<Vec<_>>();
    assert_eq!(
        parameters.len(),
        3,
        "this consumer checks the retained three-input authored question"
    );
    let declaration = format!("({} : Bool)", parameters.join(" "));
    let arguments = parameters.join(" ");
    let cases = parameters.iter().map(|p| format!("cases {p} <;> ")).collect::<String>();
    let args = format!(
        "[{}]",
        parameters.iter().map(|p| format!(".bool {p}")).collect::<Vec<_>>().join(",")
    );
    let env = entry
        .params
        .iter()
        .zip(&parameters)
        .rev()
        .map(|((id, _), p)| format!("({}, .bool {p})", id.index()))
        .collect::<Vec<_>>()
        .join(",");
    assert_eq!(witness.parameters.len(), entry.params.len());
    let entry_environment = witness
        .parameters
        .iter()
        .zip(&parameters)
        .map(|((_, name), value)| format!("({}, {value})", literal(name.bytes())))
        .collect::<Vec<_>>()
        .join(",");
    let entry_bindings = witness
        .parameters
        .iter()
        .zip(&entry.params)
        .map(|((id, name), (expected, _))| {
            assert_eq!(id, expected);
            format!("({}, {})", id.index(), literal(name.bytes()))
        })
        .collect::<Vec<_>>()
        .join(",");
    let mut post_names = Vec::new();
    let mut post_bindings = Vec::new();
    let mut post_environment = Vec::new();
    for (name, binding) in &formula.bindings {
        assert_eq!(binding.sort, trust_ir::proof::ClauseSort::Bool);
        let place = match binding.place {
            trust_ir::proof::ClausePlace::Param { index } => format!(".param {index}"),
            trust_ir::proof::ClausePlace::ResultSlot { index } => format!(".result {index}"),
            _ => panic!("untranslated contract place"),
        };
        let value = match binding.place {
            trust_ir::proof::ClausePlace::Param { index } => {
                parameters[usize::try_from(index).unwrap()].as_str()
            }
            trust_ir::proof::ClausePlace::ResultSlot { index: 0 } => "r",
            _ => panic!("untranslated contract value"),
        };
        post_environment.push(format!("({}, {value})", literal(name.bytes())));
        post_names.push(literal(name.bytes()));
        post_bindings.push(format!("({}, {place})", literal(name.bytes())));
    }
    assert_eq!(
        post.free_vars().into_iter().collect::<BTreeSet<_>>(),
        formula.bindings.iter().map(|(name, _)| name.clone()).collect()
    );
    let post_names = post_names.join(",");
    let post_bindings = post_bindings.join(",");
    let post_environment = post_environment.join(",");
    let post_expression = native_boolean_claim::expression(&post, 0).unwrap();
    let post_bytes = literal(formula.payload.bytes());
    let vc_expression = native_boolean_claim::expression(&vc, 0).unwrap();
    let vc_payload = &witness.derived_request.obligations[0].claim.payload;
    let vc_json = native_boolean_claim::json(
        &serde_json::from_str(vc_payload).unwrap(),
        native_boolean_claim::layout(vc_payload),
        0,
    )
    .unwrap();
    let vc_bytes = literal(vc_payload.bytes());
    let input_values = parameters.join(",");
    let bytes = trust_ir::binary::serialize_module(&bundle.module).unwrap();
    assert_eq!(trust_ir::binary::deserialize_module(&bytes).unwrap(), bundle.module);
    let mut changed = bundle.clone();
    let Inst::CondBr { then_target, else_target, .. } =
        &mut changed.module.functions[0].blocks[entry_index].body[0].inst
    else {
        panic!("branch entry")
    };
    std::mem::swap(then_target, else_target);
    refresh(&mut changed);
    changed.validate().unwrap();
    assert!(trust_ir_build::validate_module(&changed.module).is_empty());
    assert!(
        verify_trust_ir_body_contracts(&changed)
            .unwrap()
            .iter()
            .all(|row| row.status == trust_wp_lib::VerifyBundleStatus::Failed)
    );
    assert!(replay_trust_ir_body_contracts(&changed, results).is_err());
    assert!(
        replay_trust_ir_body_translation_witnesses(&changed, std::slice::from_ref(witness))
            .is_err()
    );
    let wrong_bytes = trust_ir::binary::serialize_module(&changed.module).unwrap();
    std::fs::write(
        scratch.join("mutated-body-native.json"),
        serde_json::to_vec_pretty(&changed).unwrap(),
    )
    .unwrap();

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
    let changed_vc_expression = native_boolean_claim::expression(&changed_vc_predicate, 0).unwrap();
    let changed_vc_payload = &changed_vc.derived_request.obligations[0].claim.payload;
    let changed_vc_json = native_boolean_claim::json(
        &serde_json::from_str(changed_vc_payload).unwrap(),
        native_boolean_claim::layout(changed_vc_payload),
        0,
    )
    .unwrap();
    let changed_vc_bytes = literal(changed_vc_payload.bytes());
    std::fs::write(
        scratch.join("mutated-vc-request.json"),
        serde_json::to_vec_pretty(&changed_vc.derived_request).unwrap(),
    )
    .unwrap();

    let mut changed_contract = bundle.clone();
    let original_contract = changed_contract
        .module
        .proof_obligations
        .iter_mut()
        .find(|row| row.id == witness.contracts[0].0)
        .unwrap()
        .formula
        .as_mut()
        .unwrap();
    assert_eq!(original_contract.schema, "trust-wp.pure-expr.v1");
    assert!(original_contract.smtlib.is_none());
    original_contract.payload = format!("!({})", original_contract.payload);
    refresh(&mut changed_contract);
    changed_contract.validate().unwrap();
    assert!(trust_ir_build::validate_module(&changed_contract.module).is_empty());
    assert!(
        verify_trust_ir_body_contracts(&changed_contract)
            .unwrap()
            .iter()
            .all(|row| row.status == trust_wp_lib::VerifyBundleStatus::Failed)
    );
    assert!(replay_trust_ir_body_contracts(&changed_contract, results).is_err());
    assert!(
        replay_trust_ir_body_translation_witnesses(
            &changed_contract,
            std::slice::from_ref(witness)
        )
        .is_err()
    );
    let changed_post = original_contract_predicate(
        changed_contract.module.proof_obligations[0].formula.as_ref().unwrap(),
    );
    let changed_post_expression = native_boolean_claim::expression(&changed_post, 0).unwrap();
    let changed_post_bytes = literal(
        changed_contract
            .module
            .proof_obligations
            .iter()
            .find(|row| row.id == witness.contracts[0].0)
            .unwrap()
            .formula
            .as_ref()
            .unwrap()
            .payload
            .bytes(),
    );
    let changed_contract_blob =
        literal(trust_ir::binary::serialize_module(&changed_contract.module).unwrap());
    std::fs::write(
        scratch.join("mutated-contract-native.json"),
        serde_json::to_vec_pretty(&changed_contract).unwrap(),
    )
    .unwrap();
    let blob = literal(bytes.iter().copied());
    let wrong_blob = literal(wrong_bytes);
    let model = module_literal(&bundle.module);
    let wrong_model = module_literal(&changed.module);
    let plan =
        plan(&witness.plan, &bundle.module.func_types[function.ty.index() as usize].returns[0]);
    let identity = format!(
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
        literal(formula.payload.bytes()),
        literal(witness.derived_request.obligations[0].claim.payload.bytes())
    );
    let fid = witness.function.index();
    let signature = function.ty.index();
    let original_relation = "((p0 && (r == p1)) || (!p0 && (r == p2)))";
    let normalization = execution_normalization(
        &declaration,
        fid,
        &arguments,
        &args,
        &format!("∃ r, vs = [.bool r] ∧ {original_relation} = true"),
        &format!("∃ r, vs = [.bool r] ∧ (!{original_relation}) = true"),
    );
    let source = format!(
        r#"import SemRBooleanClaimText
set_option maxRecDepth 8192
namespace {module_name}
open SemR SemRBooleanWP SemRBooleanWPComposition SemRBooleanWPBranches SemRNativeWPPlan
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
def postNames : List SemRBooleanClaim.Name := [{post_names}]
def postBindings : List (SemRBooleanClaim.Name × SemRBooleanClaim.Place) := [{post_bindings}]
def entryBindings : List (Nat × SemRBooleanClaim.Name) := [{entry_bindings}]
def postExpression : SemRBooleanClaim.Expr := {post_expression}
def vcBytes : SemRBooleanClaim.Bytes := {vc_bytes}
def vcJson : SemRBooleanClaim.Json := {vc_json}
def vcExpression : SemRBooleanClaim.Expr := {vc_expression}
def changedPostBytes : SemRBooleanClaim.Bytes := {changed_post_bytes}
def changedPostExpression : SemRBooleanClaim.Expr := {changed_post_expression}
def changedVCBytes : SemRBooleanClaim.Bytes := {changed_vc_bytes}
def changedVCJson : SemRBooleanClaim.Json := {changed_vc_json}
def changedVCExpression : SemRBooleanClaim.Expr := {changed_vc_expression}
theorem post_decoded : SemRBooleanClaim.decodeText 4096 postNames postBytes = some postExpression := rfl
theorem vc_encoded : SemRBooleanClaim.encodeJson 4096 vcJson = some vcBytes := rfl
theorem vc_decoded : SemRBooleanClaim.decodeClaim 4096 vcJson = some vcExpression := rfl
theorem changed_post_decoded : SemRBooleanClaim.decodeText 4096 postNames changedPostBytes = some changedPostExpression := rfl
theorem changed_vc_encoded : SemRBooleanClaim.encodeJson 4096 changedVCJson = some changedVCBytes := rfl
theorem changed_vc_decoded : SemRBooleanClaim.decodeClaim 4096 changedVCJson = some changedVCExpression := rfl
def initial {declaration} (depth : Nat) : Core :=
  {{ fn := model.functions[0], sig := model.funcTys[{signature}], block := model.functions[0].blocks[{entry_index}], pc := 0,
     env := [{env}], depth := depth, stack := [], openFrames := [], nextFrame := 0, mem := Mem.empty }}
theorem entry_environment {declaration} : SemRBooleanClaim.entryEnv entryBindings (initial {arguments} 0) = some [{entry_environment}] := rfl
theorem contract_environment {declaration} (r : Bool) : SemRBooleanClaim.contractEnv postBindings [{input_values}] r = some [{post_environment}] := rfl
def post {declaration} (r : Bool) : Bool := (do
  let bindings ← SemRBooleanClaim.contractEnv postBindings [{input_values}] r
  SemRBooleanClaim.checkedText 4096 postBytes postNames bindings).getD false
def vc {declaration} : Bool := (do
  let bindings ← SemRBooleanClaim.entryEnv entryBindings (initial {arguments} 0)
  SemRBooleanClaim.checkedJson 4096 vcBytes vcJson bindings).getD false
def changedVC {declaration} : Bool := (do
  let bindings ← SemRBooleanClaim.entryEnv entryBindings (initial {arguments} 0)
  SemRBooleanClaim.checkedJson 4096 changedVCBytes changedVCJson bindings).getD false
def changedPost {declaration} (r : Bool) : Bool := (do
  let bindings ← SemRBooleanClaim.contractEnv postBindings [{input_values}] r
  SemRBooleanClaim.checkedText 4096 changedPostBytes postNames bindings).getD false
def holds {declaration} (vs : List Val) : Prop := ∃ r, vs = [.bool r] ∧ post {arguments} r = true
theorem starts {declaration} (depth : Nat) : start model {fid} {args} depth = .ok (initial {arguments} depth) := by
  {cases} rfl
theorem vc_to_wp {declaration} (depth : Nat) (hvc : vc {arguments} = true) : wp model (holds {arguments}) plan (initial {arguments} depth) := by
  {cases} simpa [vc,post,holds,wp,plan,model,initial,
    SemRBooleanClaim.checkedJson,SemRBooleanClaim.checkedTypedJson,SemRBooleanClaim.checkedText,vc_encoded,vc_decoded,post_decoded,
    entry_environment,contract_environment,
    SemRBooleanClaim.eval,SemRBooleanClaim.evalTyped,SemRBooleanClaim.lookup,SemRBooleanClaim.Binary.apply,vcExpression,postExpression,scalarWP,scalarWPWithUInt,constWP,copyWP,selectWP,writeBool,next,
    conditionalWP,jumpWP,argsWP,returnWP,constNode,copyNode,selectNode,branchNode,conditionalNode,returnNode,
    findBlock,nth?,bindParams,lookupEnv,expectTy,Val.ty,Ty.beq,Module.pointerBits,ok_bind] using hvc
theorem vc_valid {declaration} : vc {arguments} = true := by
  {cases} simp [vc,SemRBooleanClaim.checkedJson,SemRBooleanClaim.checkedTypedJson,vc_encoded,vc_decoded,
    entry_environment,
    SemRBooleanClaim.eval,SemRBooleanClaim.evalTyped,SemRBooleanClaim.lookup,SemRBooleanClaim.Binary.apply,vcExpression]
-- The retained authored question is also checked against its nontrivial
-- original Boolean relation, independently of the emitted VC and program.
theorem original_postcondition (p0 p1 p2 r : Bool) :
  post p0 p1 p2 r = {original_relation} := by
  cases p0 <;> cases p1 <;> cases p2 <;> cases r <;>
    simp [post,SemRBooleanClaim.checkedText,post_decoded,contract_environment,
      SemRBooleanClaim.eval,SemRBooleanClaim.evalTyped,SemRBooleanClaim.lookup,
      SemRBooleanClaim.Binary.apply,postExpression]
theorem contract_nontrivial : post true false true false = true ∧ post true false true true = false := by
  simp [original_postcondition]
def ExecutionClaim : Prop := ∀ {declaration} (depth : Nat), ∃ fuel vs,
  runBlob blob {fid} {args} fuel depth = .ok (.ret vs) ∧ holds {arguments} vs
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
  runBlob wrongBlob {fid} {args} fuel depth = .ok (.ret vs) ∧ holds {arguments} vs
theorem changed_postcondition (p0 p1 p2 r : Bool) : changedPost p0 p1 p2 r = !(post p0 p1 p2 r) := by
  cases p0 <;> cases p1 <;> cases p2 <;> cases r <;>
    simp [changedPost,post,SemRBooleanClaim.checkedText,changed_post_decoded,post_decoded,
      contract_environment,SemRBooleanClaim.eval,SemRBooleanClaim.evalTyped,SemRBooleanClaim.lookup,
      SemRBooleanClaim.Binary.apply,postExpression,changedPostExpression]
theorem changed_vc_false {declaration} : changedVC {arguments} = false := by
  {cases} simp [changedVC,SemRBooleanClaim.checkedJson,SemRBooleanClaim.checkedTypedJson,changed_vc_encoded,changed_vc_decoded,
    entry_environment,
    SemRBooleanClaim.eval,SemRBooleanClaim.evalTyped,changedVCExpression]
def WrongContract : Prop := ∀ {declaration} (depth : Nat), ∃ fuel vs,
  runBlob changedContractBlob {fid} {args} fuel depth = .ok (.ret vs) ∧ ∃ r, vs = [.bool r] ∧ changedPost {arguments} r = true
def WrongVC : Prop := ∀ {declaration}, changedVC {arguments} = true
def WrongIdentity : Prop := BoundTranslation {{ identity with requestId := identity.requestId + 1 }} ExecutionClaim
{normalization}
#print axioms bound_execution
#print axioms original_execution_roundtrip
#print axioms original_vc_roundtrip
end {module_name}
"#
    );
    std::fs::write(scratch.join("original.tirb"), bytes).unwrap();
    std::fs::write(scratch.join("witness.json"), serde_json::to_vec_pretty(witness).unwrap())
        .unwrap();
    compile_lean(scratch, family, module_name, &source);
}

/// Normalize only through already checked decoder and authored-postcondition
/// equations. The original raw-byte questions retain their complete domains.
fn execution_normalization(
    declaration: &str,
    fid: impl std::fmt::Display,
    arguments: &str,
    inputs: &str,
    result: &str,
    changed_result: &str,
) -> String {
    format!(
        r#"def ModelExecution : Prop := ∀ {declaration} (depth : Nat), ∃ fuel vs,
  runFunction model {fid} {inputs} fuel depth = .ret vs ∧ {result}
def ModelWrongBody : Prop := ∀ {declaration} (depth : Nat), ∃ fuel vs,
  runFunction wrongModel {fid} {inputs} fuel depth = .ret vs ∧ {result}
def ModelWrongContract : Prop := ∀ {declaration} (depth : Nat), ∃ fuel vs,
  runFunction model {fid} {inputs} fuel depth = .ret vs ∧ {changed_result}
theorem execution_model_equiv : ExecutionClaim ↔ ModelExecution := by
  simp only [ExecutionClaim, ModelExecution, SemR.runBlob, decoded,
    Except.ok.injEq, holds, original_postcondition]
theorem wrong_body_model_equiv : WrongBody ↔ ModelWrongBody := by
  simp only [WrongBody, ModelWrongBody, SemR.runBlob, wrong_decoded,
    Except.ok.injEq, holds, original_postcondition]
theorem wrong_contract_model_equiv : WrongContract ↔ ModelWrongContract := by
  simp only [WrongContract, ModelWrongContract, SemR.runBlob,
    changed_contract_decoded, Except.ok.injEq, changed_postcondition,
    original_postcondition]
theorem model_execution : ModelExecution := execution_model_equiv.mp execution
theorem original_execution_roundtrip : ExecutionClaim :=
  execution_model_equiv.mpr model_execution
def VCClaim : Prop := ∀ {declaration}, vc {arguments} = true
def ModelVC : Prop := ∀ {declaration}, (true : Bool) = true
def ModelWrongVC : Prop := ∀ {declaration}, (false : Bool) = true
theorem vc_model_equiv : VCClaim ↔ ModelVC := by
  simp only [VCClaim, ModelVC, vc_valid]
theorem wrong_vc_model_equiv : WrongVC ↔ ModelWrongVC := by
  simp only [WrongVC, ModelWrongVC, changed_vc_false]
theorem model_vc : ModelVC := vc_model_equiv.mp vc_valid
theorem original_vc_roundtrip : VCClaim := vc_model_equiv.mpr model_vc
"#
    )
}

fn compile_lean(scratch: &Path, family: &Path, module_name: &str, source: &str) {
    let path = scratch.join(format!("{module_name}.lean"));
    std::fs::write(&path, source).unwrap();
    let output = Command::new(clean_olean::pinned_lean_binary().unwrap())
        .env("LEAN_PATH", family)
        .arg("--root")
        .arg(scratch)
        .arg("-o")
        .arg(path.with_extension("olean"))
        .arg(&path)
        .output()
        .unwrap();
    std::fs::write(scratch.join("lean.stdout"), &output.stdout).unwrap();
    std::fs::write(scratch.join("lean.stderr"), &output.stderr).unwrap();
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

/// Propose data from the existing parser/encoder. Both decoding equations and
/// equality with complete actual bytes are proved inside the kernel; Rust's
/// interpretation and its JSON feature's map order are not proof premises.
fn boolean_codec_artifact(scratch: &Path, family: &Path) -> Vec<Name> {
    use trust_wp_vc::contract_parser::parse_contract;
    let mut source = String::from(
        "import SemRBooleanClaimText\nset_option maxRecDepth 8192\nnamespace NativeBooleanCodec\nopen SemRBooleanClaim\n",
    );
    let mut targets = Vec::new();
    let mut payloads = Vec::new();
    let inputs = [
        "true",
        "false",
        "(source_x : bool)",
        "!(source_x : bool)",
        "(source_x : bool) && (other_y : bool)",
        "(source_x : bool) || (other_y : bool)",
        "(source_x : bool) ==> (other_y : bool)",
        "(source_x : bool) == (other_y : bool)",
        "(source_x : bool) != (other_y : bool)",
        "if (source_x : bool) { (other_y : bool) } else { (answer : bool) }",
    ];
    for (index, text) in inputs.into_iter().enumerate() {
        let expression = parse_contract(text).unwrap();
        let claim = trust_wp_lib::trust_ir_body::boolean_claim(&expression).unwrap();
        std::fs::write(scratch.join(format!("constructor-{index}.json")), &claim.payload).unwrap();
        let decoded =
            trust_wp_vc::verify_bundle::decode_trust_formula_v1_claim(&claim.payload).unwrap();
        assert_eq!(
            decoded,
            trust_wp_vc::verify_bundle::decode_trust_formula_v1_claim(&format!(
                "{} ",
                claim.payload
            ))
            .unwrap(),
            "the changed-byte control remains a well-formed native claim"
        );
        let proposed = native_boolean_claim::json(
            &serde_json::from_str(&claim.payload).unwrap(),
            native_boolean_claim::layout(&claim.payload),
            0,
        )
        .unwrap();
        let expression = native_boolean_claim::expression(&expression, 0).unwrap();
        let names = "[[115,111,117,114,99,101,95,120],[111,116,104,101,114,95,121],[97,110,115,119,101,114]]";
        let text_bytes = literal(text.bytes());
        let json_bytes = literal(claim.payload.bytes());
        source.push_str(&format!(
            r#"def expression{index} : Expr := {expression}
def names{index} : List Name := {names}
def text{index} : Bytes := {text_bytes}
def json{index} : Json := {proposed}
def bytes{index} : Bytes := {json_bytes}
theorem text_decoded{index} : decodeText 4096 names{index} text{index} = some expression{index} := rfl
theorem json_encoded{index} : encodeJson 4096 json{index} = some bytes{index} := rfl
theorem json_decoded{index} : decodeClaim 4096 json{index} = some (lower expression{index}) := rfl
theorem text_json_agree{index} (env : Env) :
    checkedText 4096 text{index} names{index} env = checkedJson 4096 bytes{index} json{index} env := by
  rw [checked_text_eval _ _ _ _ _ text_decoded{index},
    checked_json_eval _ _ _ _ _ json_encoded{index} json_decoded{index}, lower_sound]
theorem changed_text_refused{index} : decodeText 4096 names{index} (text{index} ++ [33]) = none := rfl
theorem changed_json_bytes_refused{index} (env : Env) :
    checkedJson 4096 (bytes{index} ++ [32]) json{index} env = none := by
  simp only [checkedJson, checkedTypedJson, json_encoded{index}]
  have different : bytes{index} ≠ bytes{index} ++ [32] := by decide
  simp [different]
"#
        ));
        for short in [
            "text_decoded",
            "json_encoded",
            "json_decoded",
            "text_json_agree",
            "changed_text_refused",
            "changed_json_bytes_refused",
        ] {
            targets.push(Name::from_string(&format!("NativeBooleanCodec.{short}{index}")));
        }
        payloads.push(serde_json::json!({"original_text": text, "actual_claim": claim}));
    }
    // Structured VC names include opaque SSA/place keys, rather than source
    // identifiers. Keep every character admitted by the canonical native rule.
    let ssa_name = "_v0#s1.field[_i]*@2-off;min=3";
    let ssa_expression = trust_wp_vc::formula::PureExpr::Var(
        ssa_name.into(),
        Some(trust_wp_vc::formula::ExprSort::Bool),
    );
    let ssa_claim = trust_wp_lib::trust_ir_body::boolean_claim(&ssa_expression).unwrap();
    assert_eq!(
        trust_wp_vc::verify_bundle::decode_trust_formula_v1_claim(&ssa_claim.payload).unwrap(),
        ssa_expression
    );
    let ssa_json = native_boolean_claim::json(
        &serde_json::from_str(&ssa_claim.payload).unwrap(),
        native_boolean_claim::layout(&ssa_claim.payload),
        0,
    )
    .unwrap();
    let ssa_bytes = literal(ssa_claim.payload.bytes());
    let ssa_expression = native_boolean_claim::expression(&ssa_expression, 0).unwrap();
    source.push_str(&format!("def ssaJson : Json := {ssa_json}\ndef ssaBytes : Bytes := {ssa_bytes}\ndef ssaExpression : Expr := {ssa_expression}\ntheorem ssa_name_encoded : encodeJson 4096 ssaJson = some ssaBytes := rfl\ntheorem ssa_name_decoded : decodeClaim 4096 ssaJson = some ssaExpression := rfl\n"));
    for short in ["ssa_name_encoded", "ssa_name_decoded"] {
        targets.push(Name::from_string(&format!("NativeBooleanCodec.{short}")));
    }
    payloads
        .push(serde_json::json!({"canonical_ssa_place_name": ssa_name, "actual_claim": ssa_claim}));
    for (index, name) in ["source::x", "β"].into_iter().enumerate() {
        let expression = trust_wp_vc::formula::PureExpr::Var(
            name.into(),
            Some(trust_wp_vc::formula::ExprSort::Bool),
        );
        let claim = trust_wp_lib::trust_ir_body::boolean_claim(&expression).unwrap();
        assert!(trust_wp_vc::verify_bundle::decode_trust_formula_v1_claim(&claim.payload).is_err());
        let proposed = native_boolean_claim::json(
            &serde_json::from_str(&claim.payload).unwrap(),
            native_boolean_claim::layout(&claim.payload),
            0,
        )
        .unwrap();
        let payload = literal(claim.payload.bytes());
        source.push_str(&format!("def refusedNameJson{index} : Json := {proposed}\ndef refusedNameBytes{index} : Bytes := {payload}\ntheorem unsupported_name_encoded{index} : encodeJson 4096 refusedNameJson{index} = some refusedNameBytes{index} := rfl\ntheorem unsupported_name_refused{index} : decodeClaim 4096 refusedNameJson{index} = none := rfl\n"));
        for short in ["unsupported_name_encoded", "unsupported_name_refused"] {
            targets.push(Name::from_string(&format!("NativeBooleanCodec.{short}{index}")));
        }
        payloads.push(serde_json::json!({"unsupported_native_name": name, "actual_claim": claim}));
    }
    source.push_str(
        r#"theorem duplicate_contract_binding_refused :
    contractEnv [([120], .param 0), ([120], .result 0)] [true] false = none := rfl
theorem unsupported_result_slot_refused :
    contractEnv [([120], .result 1)] [true] false = none := rfl
theorem unbound_text_refused : decodeText 4096 [] [120] = none := rfl
theorem duplicate_text_binding_refused : decodeText 4096 [[120], [120]] [120] = none := rfl
theorem unsupported_arithmetic_refused : decodeText 4096 [] [49,32,43,32,50] = none := rfl
end NativeBooleanCodec
"#,
    );
    for short in [
        "duplicate_contract_binding_refused",
        "unsupported_result_slot_refused",
        "unbound_text_refused",
        "duplicate_text_binding_refused",
        "unsupported_arithmetic_refused",
    ] {
        targets.push(Name::from_string(&format!("NativeBooleanCodec.{short}")));
    }
    use trust_wp_vc::formula::{ExprSort, PureExpr};
    for unsupported in [
        PureExpr::Int(1),
        PureExpr::Var("untyped".into(), None),
        PureExpr::Var("integer".into(), Some(ExprSort::Int)),
    ] {
        assert!(trust_wp_lib::trust_ir_body::boolean_claim(&unsupported).is_err());
        assert!(native_boolean_claim::expression(&unsupported, 0).is_err());
    }
    std::fs::write(
        scratch.join("actual-boolean-claims.json"),
        serde_json::to_vec_pretty(&payloads).unwrap(),
    )
    .unwrap();
    compile_lean(scratch, family, "NativeBooleanCodec", &source);
    targets
}

fn scalar_codec_targets(env: &mut Environment, family: &Path) -> BTreeSet<Name> {
    load_module_with_deps(
        env,
        "SemRScalarClaimAudit",
        &[family.to_owned(), clean_olean::require_pinned_lean_lib_path().unwrap()],
    )
    .unwrap();
    [
        "original_claim_decoded",
        "guarded_interpretation",
        "selected_value_satisfies_original",
        "full_unsigned_value_is_exact",
        "changed_result_is_false",
        "changed_bytes_refused",
        "mixed_sort_refused",
        "unbound_integer_refused",
        "integer_encoding_exact",
        "negative_encoding_exact",
        "exact_large_integer_arithmetic",
        "native_binding_uses_exact_unsigned_residue",
        "wrong_native_width_refused",
        "out_of_range_native_value_refused",
        "signed_native_value_refused",
        "poison_native_value_refused",
        "duplicate_entry_id_refused",
        "duplicate_entry_name_refused",
        "cross_sort_contract_binding_refused",
    ]
    .into_iter()
    .map(|short| {
        let name = Name::from_string(&format!("SemRScalarClaimAudit.{short}"));
        assert!(env.get_const(&name).is_some(), "missing typed codec control {name}");
        name
    })
    .collect()
}

#[test]
fn fresh_native_wp_translation_rechecks_semr_and_refuses_proof_transfer() {
    assert_eq!(
        include_bytes!("../../../first-party/trust-ir/lean/semr/SemR.lean").as_slice(),
        include_bytes!("../../../first-party/clean/crates/clean-olean/tests/fixtures/lean/v4.30.0-rc2/semr/SemR.lean").as_slice(),
        "the checker must use the actual IR-owned semantics, byte for byte"
    );
    let family = clean_olean::test_support::compiled_fixture_dir("semr_wp");
    let mut env = Environment::for_lean_replay();
    let mut targets = BTreeSet::new();
    let mut modules = Vec::new();
    for (assignments, module_name) in [(false, "NativeWpOriginal"), (true, "NativeWpAssignments")] {
        let bundle = captured(assignments);
        let original = bundle.clone();
        let witnesses = trust_ir_native_bundle_to_body_translation_witnesses(&bundle).unwrap();
        assert_eq!(witnesses.len(), 1);
        let results = verify_trust_ir_body_contracts(&bundle).unwrap();
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].status, trust_wp_lib::VerifyBundleStatus::Verified);
        replay_trust_ir_body_contracts(&bundle, &results).unwrap();
        let root = std::env::var_os("TRUST_NATIVE_WP_TRANSLATION_EVIDENCE_DIR")
            .map(std::path::PathBuf::from)
            .unwrap_or_else(|| std::path::PathBuf::from(env!("CARGO_TARGET_TMPDIR")));
        std::fs::create_dir_all(&root).unwrap();
        let scratch = tempfile::tempdir_in(root).unwrap().keep();
        eprintln!("actual fresh native translation artifact: {}", scratch.display());
        std::fs::write(
            scratch.join("original-native.json"),
            serde_json::to_vec_pretty(&bundle).unwrap(),
        )
        .unwrap();
        std::fs::write(
            scratch.join("fresh-results.json"),
            serde_json::to_vec_pretty(&results).unwrap(),
        )
        .unwrap();
        artifact(&bundle, &witnesses[0], &results, &scratch, &family, module_name);
        load_module_with_deps(
            &mut env,
            module_name,
            &[scratch, family.clone(), clean_olean::require_pinned_lean_lib_path().unwrap()],
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
            "post_decoded",
            "vc_encoded",
            "vc_decoded",
            "changed_post_decoded",
            "changed_vc_encoded",
            "changed_vc_decoded",
            "changed_contract_decoded",
            "changed_postcondition",
            "changed_vc_false",
            "original_postcondition",
            "contract_nontrivial",
            "vc_to_wp",
            "vc_valid",
            "execution",
            "bound_execution",
            "no_body_violation",
            "WrongBody",
            "WrongContract",
            "WrongVC",
            "WrongIdentity",
        ] {
            targets.insert(Name::from_string(&format!("{module_name}.{short}")));
        }
        modules.push(module_name.to_owned());
        assert_eq!(bundle, original);
    }
    let codec_root = std::env::var_os("TRUST_NATIVE_WP_TRANSLATION_EVIDENCE_DIR")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| std::path::PathBuf::from(env!("CARGO_TARGET_TMPDIR")));
    std::fs::create_dir_all(&codec_root).unwrap();
    let codec_scratch = tempfile::tempdir_in(codec_root).unwrap().keep();
    eprintln!("actual Boolean constructor artifact: {}", codec_scratch.display());
    targets.extend(boolean_codec_artifact(&codec_scratch, &family));
    load_module_with_deps(
        &mut env,
        "NativeBooleanCodec",
        &[codec_scratch, family.clone(), clean_olean::require_pinned_lean_lib_path().unwrap()],
    )
    .unwrap();
    targets.extend(scalar_codec_targets(&mut env, &family));
    let unsigned_modules = unsigned::artifacts(&mut env, &mut targets, &family);
    assert_eq!(unsigned_modules.len(), 9, "all declared widths and control-flow shapes run");
    for module in &unsigned_modules {
        for target in ["WrongBindings", "WrongWidth"] {
            assert!(env.get_const(&Name::from_string(&format!("{module}.{target}"))).is_some());
        }
    }
    modules.extend(unsigned_modules.iter().cloned());
    // Identical SemR/stdlib facts are admitted once for the combined closure.
    // Each original native question and all its refusal goals remain distinct.
    let checked = reference_base_closed(&env, &targets, &ClosedRecheckOptions::default()).unwrap();
    eprintln!(
        "combined fresh native translation ReferenceKernel: {}",
        checked.report.verdict_sentence()
    );
    assert!(
        checked.report.passed() && checked.entry_refusals.is_empty(),
        "{:?}",
        checked.entry_refusals
    );
    assert!(targets.iter().all(|n| checked.admitted.contains(n)));
    assert!(
        checked.report.axioms_admitted.iter().all(|n| [
            "Classical.choice",
            "Quot.sound",
            "propext"
        ]
        .contains(&n.as_str()))
    );
    let mut kernel = checked.into_kernel().unwrap();
    for module in modules {
        let name = |short: &str| Name::from_string(&format!("{module}.{short}"));
        assert!(native_boolean_reaches::reaches(
            kernel.environment(),
            name("execution"),
            "SemRNativeWPPlan.wp_sound"
        ));
        // Explicitly supply both propositions to Iff.mpr. The equivalence is
        // itself closed-kernel checked, and the final declaration stays at the
        // original raw-byte question; no proxy claim replaces it.
        let normalized_transfer = |raw: &str, normalized: &str, equivalence: &str, proof: &str| {
            Expr::apps(
                Expr::const_(Name::from_string("Iff.mpr"), vec![]),
                [
                    Expr::const_(name(raw), vec![]),
                    Expr::const_(name(normalized), vec![]),
                    Expr::const_(name(equivalence), vec![]),
                    Expr::const_(name(proof), vec![]),
                ],
            )
        };
        kernel
            .add_checked(Declaration::Theorem {
                name: name("NormalizedExecutionCast"),
                level_params: vec![],
                type_: Expr::const_(name("ExecutionClaim"), vec![]),
                value: normalized_transfer(
                    "ExecutionClaim",
                    "ModelExecution",
                    "execution_model_equiv",
                    "model_execution",
                ),
            })
            .unwrap_or_else(|refusal| panic!("checked raw/model positive transfer: {refusal:?}"));
        kernel
            .add_checked(Declaration::Theorem {
                name: name("NormalizedVCCast"),
                level_params: vec![],
                type_: Expr::const_(name("VCClaim"), vec![]),
                value: normalized_transfer("VCClaim", "ModelVC", "vc_model_equiv", "model_vc"),
            })
            .unwrap_or_else(|refusal| {
                panic!("checked raw/model VC positive transfer: {refusal:?}")
            });
        let mut refusals = vec![
            ("WrongBody", "model_execution"),
            ("WrongContract", "model_execution"),
            ("WrongVC", "model_vc"),
            ("WrongIdentity", "bound_execution"),
        ];
        if unsigned_modules.contains(&module) {
            refusals
                .extend([("WrongBindings", "model_execution"), ("WrongWidth", "model_execution")]);
        }
        for (target, proof) in refusals {
            // Reuse admitted facts through checked raw/model equivalences.
            // Opaque identity keeps its unchanged raw control path.
            let value = match target {
                "WrongBody" => {
                    normalized_transfer(target, "ModelWrongBody", "wrong_body_model_equiv", proof)
                }
                "WrongContract" => normalized_transfer(
                    target,
                    "ModelWrongContract",
                    "wrong_contract_model_equiv",
                    proof,
                ),
                "WrongVC" => {
                    normalized_transfer(target, "ModelWrongVC", "wrong_vc_model_equiv", proof)
                }
                "WrongBindings" => normalized_transfer(
                    target,
                    "ModelWrongBindings",
                    "wrong_bindings_model_equiv",
                    proof,
                ),
                "WrongWidth" => {
                    normalized_transfer(target, "ModelWrongWidth", "wrong_width_model_equiv", proof)
                }
                _ => Expr::const_(name(proof), vec![]),
            };
            let started = std::time::Instant::now();
            eprintln!("native WP proof-transfer start: {module}.{target} using {module}.{proof}");
            let result = kernel.add_checked(Declaration::Theorem {
                name: name(&format!("Refused{target}")),
                level_params: vec![],
                type_: Expr::const_(name(target), vec![]),
                value,
            });
            eprintln!(
                "native WP proof-transfer finish: {module}.{target} elapsed={:?} refused={}",
                started.elapsed(),
                result.is_err()
            );
            let refusal = result.expect_err(
                "a changed body/contract/VC/identity/binding/width cannot reuse the proof",
            );
            assert!(
                matches!(
                    &refusal,
                    ReferenceRefusal::Kernel(EnvError::TypeCheckFailed {
                        source: TypeError::TypeMismatch { .. },
                        ..
                    })
                ),
                "proof transfer requires a genuine application/ordinary TypeMismatch; an explicit budget, depth, memory or interrupt refusal is NOTJUDGED: {refusal:?}"
            );
        }
    }
}
