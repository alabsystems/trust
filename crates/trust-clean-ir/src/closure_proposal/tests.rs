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

/// Exercise the public genuine-Init source owner, not a bootstrap spelling or
/// a hand-constructed environment. All retained expressions remain DATA.
#[test]
fn genuine_closed_dictionary_prefix_retains_actual_originals_and_full_roster() {
    std::thread::Builder::new()
        .stack_size(128 << 20)
        .spawn(|| {
            use trust_certify::lean_source_batch::PinnedLeanSourceWorld;
            let mut world = PinnedLeanSourceWorld::new().expect("genuine pinned Init DATA");
            let inputs = |source: String| vec![LeanSourceInput {
                module: "GenuineClosureInput".into(),
                path: "/unread-source-label/GenuineClosureInput.lean".into(),
                source,
            }];
            let batch = world.check(inputs(ORIGINAL.into()), false);
            let context = batch.accepted_context().unwrap_or_else(|| {
                panic!("genuine source errors: {:?}", batch.errors())
            });
            assert_eq!(context.owned_declarations().len(), 3);
            if let Some(directory) = std::env::var_os("TRUST_GENUINE_CLOSURE_PROPOSAL_DATA") {
                let directory = std::path::Path::new(&directory);
                std::fs::create_dir_all(directory).unwrap();
                let imported = ["UInt64", "UInt64.add", "UInt64.mul", "instHAdd", "instHMul", "instAddUInt64", "instMulUInt64"];
                let data = serde_json::json!({
                    "authority":"none; actual accepted-context DATA before proposal attempt",
                    "source_world":format!("{:?}",context.source_world()),
                    "sources":context.sources().iter().map(|s|serde_json::json!({"module":s.module,"path":s.path,"source":s.source})).collect::<Vec<_>>(),
                    "source_closure_sha256":context.source_closure_sha256(),
                    "owned_declarations_sha256":context.owned_declarations_sha256(),
                    "owned":context.owned_declarations().iter().map(|n|context.environment().get_const(n)).collect::<Vec<_>>(),
                    "imported":imported.iter().map(|n|{let n=Name::from_string(n);serde_json::json!({"constant":context.environment().get_const(&n),"external":context.environment().get_extern(&n),"implemented_by":context.environment().get_implemented_by(&n)})}).collect::<Vec<_>>(),
                });
                std::fs::write(directory.join("AcceptedBeforeProposal.json"), serde_json::to_vec_pretty(&data).unwrap()).unwrap();
            }
            let proposal = propose(
                context.environment(), context.owned_declarations(),
                &Name::from_string("EscapingOriginal.useAffine"),
            ).expect("actual genuine closed dictionary prefixes must produce DATA");
            assert_eq!(proposal.module.functions.len(), 4);
            assert_eq!(proposal.originals.len(), 3);
            assert_eq!(proposal.captures, [0, 1]);
            assert_eq!(proposal.arithmetic.len(), 2);
            for original in &proposal.originals {
                assert_eq!(context.environment().get_const(&original.constant.name), Some(&original.constant));
            }
            assert_eq!(proposal.originals.iter().map(|r| r.constant.name.clone()).collect::<BTreeSet<_>>(), *context.owned_declarations());
            for row in &proposal.arithmetic {
                let args = strip(&row.source).get_app_args();
                assert_eq!(args.len(), 6);
                assert_eq!(row.erased_prefix, args[..4].iter().map(|e| (**e).clone()).collect::<Vec<_>>());
                let dictionary = &row.erased_prefix[3];
                let dictionary_args = dictionary.get_app_args();
                assert_eq!(dictionary_args.len(), 2, "complete genuine App prefix retained");
                assert!(uint64(dictionary_args[0]));
                let ExprKind::Const(head, levels) = dictionary.get_app_fn().kind() else { panic!("genuine dictionary head") };
                assert_eq!(*head, Name::from_string(&format!("instH{}", row.operation)));
                assert_eq!(levels.len(), 1);
                assert!(matches!(levels.as_slice(), [clean_kernel::Level::Zero]));
                let ExprKind::Const(provider, provider_levels) = dictionary_args[1].kind() else { panic!("genuine dictionary provider") };
                assert_eq!(*provider, Name::from_string(&format!("inst{}UInt64", row.operation)));
                assert!(provider_levels.is_empty());
            }
            assert!(proposal.module.functions.iter().all(|f| f.body_gate == Some(BodyGate::Ungated) && f.proofs.is_empty() && f.source_provenance.is_none() && f.summary.is_none()));
            assert!(trust_ir_build::validate_module(&proposal.module).is_empty());
            assert!(!trust_ir_build::validate::validate_module_for_codegen(&proposal.module).is_empty());
            if let Some(directory) = std::env::var_os("TRUST_GENUINE_CLOSURE_PROPOSAL_DATA") {
                let directory = std::path::Path::new(&directory);
                std::fs::create_dir_all(directory).unwrap();
                let data = serde_json::json!({
                    "authority":"none; actual genuine source and untrusted logical-four-function proposal DATA only",
                    "source_world":format!("{:?}",context.source_world()),
                    "source_closure_sha256":context.source_closure_sha256(),
                    "owned_declarations_sha256":context.owned_declarations_sha256(),
                    "owned":proposal.originals.iter().map(|r|&r.constant).collect::<Vec<_>>(),
                    "arithmetic":proposal.arithmetic.iter().map(|r|serde_json::json!({"owner":r.owner,"source":r.source,"erased_prefix":r.erased_prefix,"result":r.result,"operation":r.operation})).collect::<Vec<_>>(),
                    "module":proposal.module,
                });
                std::fs::write(directory.join("GenuineProposal.json"), serde_json::to_vec_pretty(&data).unwrap()).unwrap();
            }
            let extra = world.check(inputs(format!("{ORIGINAL}\ndef sibling (x : UInt64) : UInt64 := x\n")), false);
            let extra_context = extra.accepted_context().expect("genuine extra source accepted");
            assert_eq!(extra_context.owned_declarations().len(), 4);
            assert!(propose(extra_context.environment(), extra_context.owned_declarations(), &Name::from_string("EscapingOriginal.useAffine")).unwrap_err().contains("exactly three complete owned"));
            let hostile_body = "@HAdd.hAdd UInt64 UInt64 UInt64 (@HAdd.mk UInt64 UInt64 UInt64 (fun (p : UInt64) (q : UInt64) => a * p + q)) x b";
            let hostile = world.check(inputs(ORIGINAL.replace("a * x + b", hostile_body)), false);
            let hostile_context = hostile.accepted_context().expect("actual captured dictionary source accepted");
            assert_eq!(hostile_context.owned_declarations().len(), 3);
            assert!(propose(hostile_context.environment(), hostile_context.owned_declarations(), &Name::from_string("EscapingOriginal.useAffine")).unwrap_err().contains("dictionary/type prefix"));
        }).unwrap().join().unwrap();
}

fn arithmetic_advice(
    expression: &Expr,
    budget: usize,
) -> (Result<ValueId, String>, Vec<ArithmeticProposal>, BTreeSet<usize>) {
    let mut module = ModuleBuilder::new("untrusted-dictionary-prefix-test");
    let signature = module.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut function = module.function("candidate", signature);
    let locals = entry(&mut function, &[Ty::U64, Ty::U64]);
    let mut rows = Vec::new();
    let mut used = BTreeSet::new();
    let mut budget = budget;
    let result = arithmetic(
        &mut function,
        &locals,
        expression,
        &Name::from_string("source"),
        &mut rows,
        &mut budget,
        &mut used,
    );
    (result, rows, used)
}

fn generic_dictionary(operation: &str) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string(&format!("instH{operation}")),
            vec![clean_kernel::Level::zero()],
        ),
        [Expr::const_str("UInt64"), Expr::const_str(&format!("inst{operation}UInt64"))],
    )
}

fn add_with_dictionary(dictionary: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("HAdd.hAdd"), vec![clean_kernel::Level::zero(); 3]),
        [
            Expr::const_str("UInt64"),
            Expr::const_str("UInt64"),
            Expr::const_str("UInt64"),
            dictionary,
            Expr::bvar(1),
            Expr::bvar(0),
        ],
    )
}

#[test]
fn nonclosed_wrong_or_polymorphic_prefixes_refuse_before_erasing_any_capture() {
    use clean_kernel::{FVarId, Level};
    let bridge = Expr::const_(Name::from_string("instHAdd"), vec![Level::zero()]);
    let word = Expr::const_str("UInt64");
    let provider = Expr::const_str("instAddUInt64");
    for dictionary in [
        Expr::bvar(0),
        Expr::fvar(FVarId::new(7)),
        Expr::mdata(Vec::new(), Expr::bvar(1)),
        Expr::apps(bridge.clone(), [word.clone(), Expr::bvar(0)]),
        Expr::apps(bridge.clone(), [word.clone(), Expr::fvar(FVarId::new(8))]),
        Expr::apps(bridge.clone(), [Expr::bvar(0), provider.clone()]),
        Expr::apps(bridge.clone(), [Expr::fvar(FVarId::new(9)), provider.clone()]),
        Expr::apps(Expr::bvar(0), [word.clone(), provider.clone()]),
        Expr::apps(Expr::fvar(FVarId::new(10)), [word.clone(), provider.clone()]),
        Expr::apps(bridge.clone(), [Expr::const_str("Bool"), provider.clone()]),
        Expr::apps(bridge.clone(), [word.clone(), Expr::const_str("instMulUInt64")]),
        Expr::apps(
            bridge.clone(),
            [word.clone(), Expr::const_(Name::from_string("instAddUInt64"), vec![Level::zero()])],
        ),
        Expr::apps(
            Expr::const_(Name::from_string("instHAdd"), vec![Level::succ(Level::zero())]),
            [word.clone(), provider.clone()],
        ),
        Expr::apps(
            Expr::const_(Name::from_string("instHAdd"), vec![Level::param(Name::from_string("u"))]),
            [word.clone(), provider.clone()],
        ),
        Expr::apps(bridge.clone(), [word.clone(), provider.clone(), Expr::bvar(0)]),
        Expr::app(bridge, word),
        generic_dictionary("Mul"),
    ] {
        let (result, rows, used) = arithmetic_advice(&add_with_dictionary(dictionary), 64);
        assert!(result.unwrap_err().contains("dictionary/type prefix"));
        assert!(rows.is_empty(), "unsupported prefix produced no arithmetic advice");
        assert!(used.is_empty(), "no source value was silently erased as a dictionary");
    }
}

#[test]
fn complete_metadata_and_closed_prefix_remain_data_and_budgets_still_refuse() {
    let dictionary = Expr::mdata(Vec::new(), generic_dictionary("Add"));
    let source = Expr::mdata(Vec::new(), add_with_dictionary(dictionary.clone()));
    let (result, rows, used) = arithmetic_advice(&source, 64);
    assert!(result.is_ok());
    assert_eq!(rows.len(), 1);
    assert!(matches!(rows[0].source.kind(), ExprKind::MData(..)));
    assert_eq!(rows[0].source, source);
    assert_eq!(rows[0].erased_prefix[3], dictionary);
    assert_eq!(used, BTreeSet::from([0, 1]));
    let (result, rows, _) = arithmetic_advice(&source, 0);
    assert!(result.unwrap_err().contains("node bound"));
    assert!(rows.is_empty());
}

/// Raw wire syntax is not reduced universe equality. Both forms satisfy
/// Level::is_zero(), but neither is the literal-zero candidate grammar.
#[test]
fn raw_zero_equivalent_universes_refuse_without_normalizing_prefix_data() {
    use clean_kernel::Level;
    let cases = [
        ("imax-param-zero", serde_json::json!({"IMax":[{"Param":Name::from_string("u")},"Zero"]})),
        ("max-zero-zero", serde_json::json!({"Max":["Zero","Zero"]})),
    ];
    let mut accepted = Vec::new();
    let mut outcomes = Vec::new();
    for (label, raw) in cases {
        let level: Level =
            serde_json::from_value(raw.clone()).expect("supported raw Level wire DATA");
        assert!(!matches!(&level, Level::Zero));
        assert!(level.is_zero(), "old reduced-zero predicate accepts this raw case");
        assert_eq!(
            serde_json::to_value(&level).unwrap(),
            raw,
            "raw serde must not normalize syntax"
        );
        for operation in ["Add", "Mul"] {
            let dictionary = Expr::apps(
                Expr::const_(Name::from_string(&format!("instH{operation}")), vec![level.clone()]),
                [Expr::const_str("UInt64"), Expr::const_str(&format!("inst{operation}UInt64"))],
            );
            let outer = if operation == "Add" { "HAdd.hAdd" } else { "HMul.hMul" };
            let source = Expr::apps(
                Expr::const_(Name::from_string(outer), vec![Level::zero(); 3]),
                [
                    Expr::const_str("UInt64"),
                    Expr::const_str("UInt64"),
                    Expr::const_str("UInt64"),
                    dictionary,
                    Expr::bvar(1),
                    Expr::bvar(0),
                ],
            );
            let original = source.clone();
            let (result, rows, used) = arithmetic_advice(&source, 64);
            assert_eq!(source, original, "candidate input must remain exact");
            let candidate_data = result.is_ok();
            eprintln!("raw universe {label}/{operation}: candidate_data={candidate_data}");
            outcomes.push(serde_json::json!({"case":label,"operation":operation,"raw_level":raw,"source":source,"candidate_data":candidate_data,"error":result.as_ref().err(),"arithmetic_rows":rows.len(),"used":used}));
            if candidate_data {
                accepted.push(format!("{label}/{operation}"));
            } else {
                assert!(result.unwrap_err().contains("dictionary/type prefix"));
                assert!(rows.is_empty(), "unsupported raw universe produced no arithmetic advice");
                assert!(used.is_empty(), "no capture was consumed before prefix refusal");
            }
        }
    }
    if let Some(directory) = std::env::var_os("TRUST_GENUINE_CLOSURE_PROPOSAL_DATA") {
        let directory = std::path::Path::new(&directory);
        std::fs::create_dir_all(directory).unwrap();
        std::fs::write(
            directory.join("RawUniverseCases.json"),
            serde_json::to_vec_pretty(&outcomes).unwrap(),
        )
        .unwrap();
    }
    assert!(
        accepted.is_empty(),
        "raw zero-equivalent universe prefixes produced candidate DATA: {accepted:?}"
    );
}
