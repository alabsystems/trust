use trust_certify::lean_source_batch::{CheckedLeanSourceBatch, LeanSourceInput};

use super::*;

const ORIGINAL: &str =
    include_str!("../../../trust-clean-ir-gate/probes/source_closure_refinement/Original.lean");

fn checked(source: &str) -> CheckedLeanSourceBatch {
    CheckedLeanSourceBatch::check_with_runtime_baseline(
        vec![LeanSourceInput {
            module: "ActualClosureInput".into(),
            path: "ActualClosureInput.lean".into(),
            source: source.into(),
        }],
        false,
    )
}

fn candidate(source: &str, selected: &str) -> TypedClosureProposal {
    let batch = checked(source);
    let context =
        batch.accepted_context().unwrap_or_else(|| panic!("source errors: {:?}", batch.errors()));
    if source == ORIGINAL {
        if let Some(dir) = std::env::var_os("TRUST_TYPED_CLOSURE_PROPOSAL_DATA") {
            let dir = std::path::Path::new(&dir);
            std::fs::create_dir_all(dir).unwrap();
            if !dir.join("ActualAccepted.json").exists() {
                let mut pending = context.owned_declarations().clone();
                let mut visited = BTreeSet::new();
                while let Some(name) = pending.pop_first() {
                    if !visited.insert(name.clone()) {
                        continue;
                    }
                    assert!(visited.len() < 20000, "capture dependency bound");
                    if let Some(info) = context.environment().get_const(&name) {
                        pending.extend(
                            info.type_
                                .collect_constants()
                                .into_iter()
                                .filter(|n| !visited.contains(n)),
                        );
                        if let Some(value) = &info.value {
                            pending.extend(
                                value
                                    .collect_constants()
                                    .into_iter()
                                    .filter(|n| !visited.contains(n)),
                            );
                        }
                    }
                }
                let payload = serde_json::json!({
                    "authority":"none-data-only-not-source-refinement",
                    "source_closure_sha256":context.source_closure_sha256(),
                    "owned_declarations_sha256":context.owned_declarations_sha256(),
                    "sources":context.sources().iter().map(|s|serde_json::json!({"module":s.module,"path":s.path,"source":s.source})).collect::<Vec<_>>(),
                    "aliases":context.aliases().iter().map(|a|serde_json::json!({"module":a.module,"source_index":a.source_index})).collect::<Vec<_>>(),
                    "owned":context.owned_declarations(),
                    "payloads":visited.iter().map(|n|serde_json::json!({"name":n,
                        "constant":context.environment().get_const(n),
                        "inductive":context.environment().get_inductive(n),
                        "constructor":context.environment().get_constructor(n),
                        "recursor":context.environment().get_recursor(n)})).collect::<Vec<_>>()
                });
                std::fs::write(
                    dir.join("ActualAccepted.json"),
                    serde_json::to_vec_pretty(&payload).unwrap(),
                )
                .unwrap();
            }
        }
    }
    propose(context.environment(), context.owned_declarations(), &Name::from_string(selected))
        .unwrap_or_else(|e| {
            panic!(
                "{e}\nactual payloads: {:?}",
                context
                    .owned_declarations()
                    .iter()
                    .map(|n| context.environment().get_const(n))
                    .collect::<Vec<_>>()
            )
        })
}

#[test]
fn actual_accepted_source_constructs_complete_canonical_candidate_data() {
    let proposal = candidate(ORIGINAL, "EscapingOriginal.useAffine");
    assert_eq!(proposal.module.functions.len(), 4);
    assert_eq!(proposal.originals.len(), 3);
    assert_eq!(proposal.captures, [0, 1]);
    assert_eq!(proposal.module.closure_types.len(), 1);
    assert!(proposal.module.functions.iter().all(|f| !f.blocks.is_empty()
        && f.calling_conv == CallingConv::Rust
        && f.body_gate == Some(BodyGate::Ungated)
        && f.proofs.is_empty()
        && f.source_provenance.is_none()
        && f.summary.is_none()));
    assert!(trust_ir_build::validate_module(&proposal.module).is_empty());
    let bytes = trust_ir::binary::serialize_module(&proposal.module).unwrap();
    let back = trust_ir::binary::deserialize_module(&bytes).unwrap();
    assert_eq!(back, proposal.module);
    assert_eq!(bytes, trust_ir::binary::serialize_module(&back).unwrap());
    assert!(!trust_ir_build::validate::validate_module_for_codegen(&back).is_empty());
    if let Some(dir) = std::env::var_os("TRUST_TYPED_CLOSURE_PROPOSAL_DATA") {
        let dir = std::path::Path::new(&dir);
        std::fs::create_dir_all(dir).unwrap();
        std::fs::write(
            dir.join("Module.json"),
            serde_json::to_vec_pretty(&proposal.module).unwrap(),
        )
        .unwrap();
        std::fs::write(dir.join("Module.tmbc"), bytes).unwrap();
        std::fs::write(
            dir.join("Module.compact.json"),
            serde_json::to_vec(&proposal.module).unwrap(),
        )
        .unwrap();
        std::fs::write(dir.join("Original.lean"), ORIGINAL).unwrap();
        write_mutants(dir, &proposal);
        std::fs::write(
            dir.join("Originals.json"),
            serde_json::to_vec_pretty(
                &proposal.originals.iter().map(|r| &r.constant).collect::<Vec<_>>(),
            )
            .unwrap(),
        )
        .unwrap();
        let batch = checked(ORIGINAL);
        let context = batch.accepted_context().unwrap();
        let mut dependencies = BTreeSet::new();
        for row in &proposal.originals {
            dependencies.extend(row.constant.type_.collect_constants());
            dependencies.extend(row.constant.value.as_ref().unwrap().collect_constants());
        }
        std::fs::write(
            dir.join("Dependencies.json"),
            serde_json::to_vec_pretty(
                &dependencies
                    .iter()
                    .map(|name| (name, context.environment().get_const(name)))
                    .collect::<Vec<_>>(),
            )
            .unwrap(),
        )
        .unwrap();
    }
}

fn write_mutants(dir: &std::path::Path, proposal: &TypedClosureProposal) {
    use trust_ir::inst::{BinOp, Inst};
    let mut mutants = Vec::new();
    let mut module = proposal.module.clone();
    let target = module.functions.iter_mut().find(|f| f.id == proposal.lifted_function).unwrap();
    let node = target.blocks[0]
        .body
        .iter_mut()
        .find(|n| matches!(n.inst, Inst::BinOp { op: BinOp::Mul, .. }))
        .unwrap();
    if let Inst::BinOp { op, .. } = &mut node.inst {
        *op = BinOp::Add;
    }
    mutants.push(("target-mul-to-add", module));
    for label in [
        "wrong-target",
        "swapped-captures",
        "erased-target-param",
        "apply-arity",
        "target-convention-c",
        "omitted-original",
    ] {
        let mut module = proposal.module.clone();
        match label {
            "wrong-target" | "swapped-captures" => {
                let node = module
                    .functions
                    .iter_mut()
                    .flat_map(|f| &mut f.blocks)
                    .flat_map(|b| &mut b.body)
                    .find(|n| matches!(n.inst, Inst::MakeClosure { .. }))
                    .unwrap();
                if let Inst::MakeClosure { func, captures, .. } = &mut node.inst {
                    if label == "wrong-target" {
                        *func = proposal.originals[0].function;
                    } else {
                        captures.swap(0, 1);
                    }
                }
            }
            "erased-target-param" | "target-convention-c" => {
                let erased_signature = if label == "erased-target-param" {
                    let target =
                        module.functions.iter().find(|f| f.id == proposal.lifted_function).unwrap();
                    let mut signature = module.func_type(target.ty).unwrap().clone();
                    signature.params.pop();
                    Some(module.add_func_type(signature).unwrap())
                } else {
                    None
                };
                let target =
                    module.functions.iter_mut().find(|f| f.id == proposal.lifted_function).unwrap();
                if let Some(signature) = erased_signature {
                    target.ty = signature;
                    target.blocks[0].params.pop();
                } else {
                    target.calling_conv = CallingConv::C;
                }
            }
            "apply-arity" => {
                let node = module
                    .functions
                    .iter_mut()
                    .flat_map(|f| &mut f.blocks)
                    .flat_map(|b| &mut b.body)
                    .find(|n| matches!(n.inst, Inst::CallIndirect { .. }))
                    .unwrap();
                if let Inst::CallIndirect { args, .. } = &mut node.inst {
                    args.clear();
                }
            }
            "omitted-original" => {
                module.functions.retain(|f| f.id != proposal.originals[2].function)
            }
            _ => unreachable!(),
        }
        mutants.push((label, module));
    }
    let dir = dir.join("mutants");
    std::fs::create_dir_all(&dir).unwrap();
    for (name, module) in mutants {
        assert_ne!(module, proposal.module);
        std::fs::write(
            dir.join(format!("{name}.json")),
            serde_json::to_vec_pretty(&module).unwrap(),
        )
        .unwrap();
        std::fs::write(
            dir.join(format!("{name}.tmbc")),
            trust_ir::binary::serialize_module(&module).unwrap(),
        )
        .unwrap();
    }
}

#[test]
fn body_capture_and_application_changes_change_real_candidate() {
    let base = candidate(ORIGINAL, "EscapingOriginal.useAffine");
    for (old, new) in [
        ("a * x + b", "a + x + b"),
        ("a * x + b", "a * x - b"),
        ("a * x + b", "b * x + a"),
        ("a * x + b", "a * x"),
        ("makeAffine a b\n", "makeAffine b a\n"),
        (":= f x\n", ":= f (x + x)\n"),
    ] {
        let source = ORIGINAL.replace(old, new);
        assert_ne!(source, ORIGINAL);
        let changed = candidate(&source, "EscapingOriginal.useAffine");
        assert_ne!(base.module, changed.module, "{old} -> {new}");
        assert_ne!(
            base.originals.iter().map(|r| &r.constant).collect::<Vec<_>>(),
            changed.originals.iter().map(|r| &r.constant).collect::<Vec<_>>()
        );
    }
}

#[test]
fn source_names_do_not_select_a_frozen_function_table() {
    let renamed = ORIGINAL
        .replace("EscapingOriginal", "ActualInput")
        .replace("makeAffine", "buildCaptured")
        .replace("apply64", "invokeCaptured")
        .replace("useAffine", "runCaptured");
    let proposal = candidate(&renamed, "ActualInput.runCaptured");
    assert_eq!(proposal.module.functions.len(), 4);
    assert!(
        proposal.originals.iter().all(|r| r.constant.name.to_string().starts_with("ActualInput."))
    );
    assert!(proposal.module.functions.iter().all(|r| !r.name.contains("EscapingOriginal")));
}

#[test]
fn unsupported_or_extra_owned_source_refuses_whole_candidate() {
    for source in [
        format!("{ORIGINAL}\ndef sibling (x : UInt64) : UInt64 := x\n"),
        ORIGINAL.replace("a * x + b", "a / x + b"),
        ORIGINAL.replace("let f := makeAffine a b\n  apply64 f x", "makeAffine a b x"),
    ] {
        let batch = checked(&source);
        let context = batch.accepted_context().expect("source accepted");
        assert!(
            propose(
                context.environment(),
                context.owned_declarations(),
                &Name::from_string("EscapingOriginal.useAffine")
            )
            .is_err()
        );
    }
}

/// A source dictionary can contain a live capture outside the two operands.
/// Reading just HAdd's final operands would turn this source into x+b and drop
/// a. Such advice stays outside the bounded proposal grammar; no Rust result
/// here establishes the semantics of the supported Prelude instance either.
#[test]
fn noncanonical_dictionary_capture_refuses_the_whole_proposal() {
    let body = "@HAdd.hAdd UInt64 UInt64 UInt64 (@HAdd.mk UInt64 UInt64 UInt64 (fun (p : UInt64) (q : UInt64) => a * p + q)) x b";
    let source = ORIGINAL.replace("a * x + b", body);
    let batch = checked(&source);
    let context =
        batch.accepted_context().unwrap_or_else(|| panic!("source errors: {:?}", batch.errors()));
    assert_eq!(context.owned_declarations().len(), 3);
    let error = propose(
        context.environment(),
        context.owned_declarations(),
        &Name::from_string("EscapingOriginal.useAffine"),
    )
    .unwrap_err();
    assert!(error.contains("dictionary/type prefix"), "{error}");
}
