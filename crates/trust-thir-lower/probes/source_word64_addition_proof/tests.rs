use clean_kernel::{BinderInfo, Environment, Expr, ExprKind, Level, Name, TypeChecker};
use clean_verify::source_ir_word64_addition as connection;
use std::sync::OnceLock;
use trust_ir::{
    BlockId, CallingConv, Endianness, FuncId, Inst, Module, StructPassingPolicy, TargetInfo, Ty,
    ValueId,
};
use trust_ir_build::{
    core_execution::{
        Assembler, Catalog, Coordinate, EntryTarget, Limits, MachineModel, NatTerm,
        PendingEquality, RootReturnFrame,
    },
    scoped_local::LocalScope,
    source_addition_data::RustU64AdditionModule,
};
fn c(n: &str) -> Expr {
    Expr::const_str(n)
}
fn a(n: &str, x: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(n), x)
}
fn nat(n: u64) -> Expr {
    Expr::nat_lit(n)
}
fn list(t: &str, x: impl IntoIterator<Item = Expr>) -> Expr {
    let x: Vec<_> = x.into_iter().collect();
    x.into_iter()
        .rev()
        .fold(a("IRList.nil", [c(t)]), |tail, head| {
            a("IRList.cons", [c(t), head, tail])
        })
}
fn eq(t: Expr, l: Expr, r: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [t, l, r],
    )
}
fn refl(t: Expr, v: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [t, v],
    )
}
fn limits() -> Limits {
    Limits {
        max_operations: 4000,
        max_locals: 100,
        max_list_items: 100,
        max_lookup_candidates: 100,
        lookup_heartbeats: 5_000_000,
        lookup_cache_entries: 100_000,
    }
}
fn environment() -> &'static Environment {
    static E: OnceLock<Environment> = OnceLock::new();
    E.get_or_init(|| connection::environment().unwrap())
}
fn subject(w: &RustU64AdditionModule<'_>, source: &str) -> connection::RawAdditionSubject {
    connection::RawAdditionSubject {
        original_source: source.into(),
        original_function: w.function_name().into(),
        original_instance: actual_facts()["owner_hash"].as_str().unwrap().into(),
        module_bytes: w.original_bytes().to_vec(),
        ir_function_name: w.function_name().into(),
        function_id: w.function_id().index(),
        function_type_id: w.signature_id().index(),
        entry_block: w.entry_block().index(),
        parameter_value: w.parameter().index(),
        constant_value: w.constant().index(),
        literal: w.literal(),
        addition_value: w.addition().index(),
        return_value: w.returned().index(),
        reflected_context: w.reflected().context_term().clone(),
    }
}
fn proof(w: &RustU64AdditionModule<'_>) -> Expr {
    assert!(
        std::env::var_os("TRUST_G4_FORBID_PRODUCER").is_none(),
        "producer forbidden in fresh consumer"
    );
    let env = environment();
    let mut scope = LocalScope::new();
    let mut assem = Assembler::new(&mut scope, limits()).unwrap();
    let mut ps = Vec::new();
    let rho = assem.local(Expr::arrow(c("Nat"), c("Nat"))).unwrap();
    ps.push(rho.clone());
    let world = assem.local(Expr::type_()).unwrap();
    ps.push(world.clone());
    let mem = assem.local(c("IRByteMemoryV1")).unwrap();
    ps.push(mem.clone());
    let host = assem.local(world.term().clone()).unwrap();
    ps.push(host.clone());
    let providers = assem
        .local(a("IRByteProvidersV1", [world.term().clone()]))
        .unwrap();
    ps.push(providers.clone());
    let model = MachineModel::new(
        world.term().clone(),
        w.reflected(),
        providers.term().clone(),
    );
    let mut catalog = Catalog::new(env, w.reflected(), limits()).unwrap();
    let entry = catalog
        .rust_u64_add_literal_entry_v1(w.function_id())
        .unwrap();
    let memory_guard = EntryTarget::memory_admission(mem.term().clone());
    let memory_h = assem
        .local(eq(c("Bool"), memory_guard.clone(), c("Bool.true")))
        .unwrap();
    ps.push(memory_h.clone());
    let memory = PendingEquality::candidate(
        c("Bool"),
        memory_guard,
        c("Bool.true"),
        memory_h.term().clone(),
    );
    let word = Expr::app(rho.term().clone(), nat(0));
    let word_guard = a("ir_nat_ltb", [word.clone(), a("ir_nat_pow2", [nat(64)])]);
    let word_h = assem
        .local(eq(c("Bool"), word_guard, c("Bool.true")))
        .unwrap();
    ps.push(word_h.clone());
    let scalar = a("IRScalar.int_", [word.clone()]);
    let values = list("IRScalar", [scalar]);
    let fits = a(
        "ir_byte_value_matches_v1",
        [
            model.context().clone(),
            a("IRTy.uint_", [nat(64)]),
            a("IRScalar.int_", [word.clone()]),
        ],
    );
    let fits_proof = a(
        "ir_byte_u64_value_fits_v1",
        [model.context().clone(), word, word_h.term().clone()],
    );
    let values_proof = a(
        "ir_byte_world_and_intro_v1",
        [
            fits,
            c("Bool.true"),
            fits_proof,
            refl(c("Bool"), c("Bool.true")),
        ],
    );
    let admitted = PendingEquality::candidate(
        c("Bool"),
        entry.admission(&model, values.clone()).unwrap(),
        c("Bool.true"),
        values_proof.clone(),
    );
    let initialized = entry
        .initialize(
            &mut assem,
            &model,
            values.clone(),
            mem.term().clone(),
            host.term().clone(),
            memory,
            admitted,
        )
        .unwrap();
    // Both scalar transfers retain the actual fetched instructions and SSA map.
    let coordinate = |pc| Coordinate {
        function: w.function_id(),
        block: w.entry_block(),
        instruction: pc,
    };
    let constant = catalog.fetch(coordinate(0)).unwrap();
    let k = nat(w.literal());
    let literal_value = a("IRScalar.int_", [k.clone()]);
    let checks = constant
        .scalar_checks(&model, initialized.current(), literal_value.clone())
        .unwrap();
    let evaluated = assem
        .conversion(
            c("IRStepResult"),
            checks.evaluation,
            a("IRStepResult.value", [literal_value.clone()]),
        )
        .unwrap();
    let operands = assem
        .conversion(c("Bool"), checks.operands, c("Bool.true"))
        .unwrap();
    let result = assem
        .conversion(c("Bool"), checks.result, c("Bool.true"))
        .unwrap();
    let cstep = constant
        .scalar_value(
            &mut assem,
            &model,
            initialized.current(),
            literal_value,
            trust_ir_build::core_execution::ScalarPremises {
                evaluated,
                operands,
                result,
                before: initialized.valid().clone(),
            },
        )
        .unwrap();
    assert_eq!(cstep.current().world, initialized.current().world);
    let word = Expr::app(rho.term().clone(), nat(0));
    let limit = a("ir_nat_pow2", [nat(64)]);
    let input_bound = a(
        "ir_byte_separation_lt_of_ltb_v1",
        [word.clone(), limit.clone(), word_h.term().clone()],
    );
    let k_bound = assem
        .conversion(
            c("Bool"),
            a("ir_nat_ltb", [k.clone(), limit.clone()]),
            c("Bool.true"),
        )
        .unwrap();
    let k_lt = a(
        "ir_byte_separation_lt_of_ltb_v1",
        [k.clone(), limit.clone(), k_bound.term().clone()],
    );
    let (_conditional, evaluated, _) = assem
        .byte_add_u64_canonical(
            word.clone(),
            k.clone(),
            trust_ir_build::core_execution::PendingProof::candidate(
                a("Nat.lt", [word.clone(), limit.clone()]),
                input_bound,
            ),
            trust_ir_build::core_execution::PendingProof::candidate(
                a("Nat.lt", [k.clone(), limit.clone()]),
                k_lt,
            ),
        )
        .unwrap();
    let output = a(
        "Nat.mod",
        [
            a("Nat.add", [word.clone(), k.clone()]),
            a("Nat.succ", [nat(u64::MAX)]),
        ],
    );
    let modulo = a(
        "RustSourceWord64IRV1.modCanonical",
        [
            nat(64),
            word.clone(),
            k.clone(),
            word_h.term().clone(),
            k_bound.term().clone(),
        ],
    );
    let conditional_scalar = evaluated.right().get_app_args()[0].clone();
    let conditional_word = conditional_scalar.get_app_args()[0].clone();
    let modulo_eq = PendingEquality::candidate(c("Nat"), output.clone(), conditional_word, modulo);
    let mapper = Expr::lam(
        BinderInfo::Default,
        c("Nat"),
        a("IRStepResult.value", [a("IRScalar.int_", [Expr::bvar(0)])]),
    );
    let mapped = assem
        .congruence_function(modulo_eq, c("IRStepResult"), mapper)
        .unwrap();
    let reversed = PendingEquality::candidate(
        c("IRStepResult"),
        mapped.right().clone(),
        mapped.left().clone(),
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.symm"),
                vec![Level::succ(Level::zero())],
            ),
            [
                c("IRStepResult"),
                mapped.left().clone(),
                mapped.right().clone(),
                mapped.term().clone(),
            ],
        ),
    );
    let reversed = assem
        .convert_endpoints(
            reversed,
            evaluated.right().clone(),
            a("IRStepResult.value", [a("IRScalar.int_", [output.clone()])]),
        )
        .unwrap();
    let evaluated = assem.compose(evaluated, reversed).unwrap();
    let adding = catalog.fetch(coordinate(1)).unwrap();
    let output_scalar = a("IRScalar.int_", [output.clone()]);
    let checks = adding
        .scalar_checks(&model, cstep.current(), output_scalar.clone())
        .unwrap();
    let evaluated = assem
        .convert_endpoints(
            evaluated,
            checks.evaluation,
            a("IRStepResult.value", [output_scalar.clone()]),
        )
        .unwrap();
    let operand_proof = a(
        "ir_byte_world_and_intro_v1",
        [
            a(
                "ir_byte_value_matches_v1",
                [
                    model.context().clone(),
                    a("IRTy.uint_", [nat(64)]),
                    a("IRScalar.int_", [word.clone()]),
                ],
            ),
            a(
                "ir_byte_value_matches_v1",
                [
                    model.context().clone(),
                    a("IRTy.uint_", [nat(64)]),
                    a("IRScalar.int_", [k.clone()]),
                ],
            ),
            a(
                "ir_byte_u64_value_fits_v1",
                [model.context().clone(), word.clone(), word_h.term().clone()],
            ),
            a(
                "ir_byte_u64_value_fits_v1",
                [model.context().clone(), k.clone(), k_bound.term().clone()],
            ),
        ],
    );
    let operands =
        PendingEquality::candidate(c("Bool"), checks.operands, c("Bool.true"), operand_proof);
    let out_lt = a(
        "Nat.mod_lt",
        [
            a("Nat.add", [word, k]),
            a("Nat.succ", [nat(u64::MAX)]),
            a("Nat.zero_lt_succ", [nat(u64::MAX)]),
        ],
    );
    let out_fits = a("ir_byte_ltb_of_lt_v1", [output.clone(), limit, out_lt]);
    let fit = a(
        "ir_byte_value_matches_v1",
        [
            model.context().clone(),
            a("IRTy.uint_", [nat(64)]),
            output_scalar.clone(),
        ],
    );
    let fits_proof = a(
        "ir_byte_u64_value_fits_v1",
        [model.context().clone(), output.clone(), out_fits],
    );
    let output_values_proof = a(
        "ir_byte_world_and_intro_v1",
        [
            fit,
            c("Bool.true"),
            fits_proof,
            refl(c("Bool"), c("Bool.true")),
        ],
    );
    let result = PendingEquality::candidate(
        c("Bool"),
        checks.result,
        c("Bool.true"),
        output_values_proof.clone(),
    );
    let astep = adding
        .scalar_value(
            &mut assem,
            &model,
            cstep.current(),
            output_scalar.clone(),
            trust_ir_build::core_execution::ScalarPremises {
                evaluated,
                operands,
                result,
                before: cstep.valid().clone(),
            },
        )
        .unwrap();
    assert_eq!(astep.current().world, initialized.current().world);
    let values = list("IRScalar", [output_scalar]);
    let values_proof = output_values_proof;
    let owner = a("ir_byte_fresh_owner_v1", [mem.term().clone()]);
    let frame = RootReturnFrame {
        returning: astep.current().frame.clone(),
        legacy_memory: list("IRMemSlot", []),
        legacy_cursor: nat(0),
        memory: mem.term().clone(),
        host: host.term().clone(),
        owner: owner.clone(),
        next: a("Nat.succ", [owner]),
    };
    let site = catalog
        .fetch(Coordinate {
            function: w.function_id(),
            block: w.entry_block(),
            instruction: 2,
        })
        .unwrap();
    let target = catalog.call_target(w.function_id()).unwrap();
    let resolved = assem
        .conversion(
            a("IRList", [c("IRScalar")]),
            a(
                "ir_resolve",
                [
                    frame.current(&model).machine(),
                    list("Nat", [nat(w.returned().index() as u64)]),
                ],
            ),
            values.clone(),
        )
        .unwrap();
    let return_guard = site
        .root_return_admission(&model, &target, &frame, values.clone())
        .unwrap();
    let value_guard = a(
        "ir_byte_values_match_v1",
        [
            model.context().clone(),
            list("IRTy", [a("IRTy.uint_", [nat(64)])]),
            values,
        ],
    );
    let return_proof = a(
        "ir_byte_world_and_intro_v1",
        [
            value_guard,
            c("Bool.true"),
            values_proof,
            refl(c("Bool"), c("Bool.true")),
        ],
    );
    let returned = site
        .return_from_root(
            &mut assem,
            &model,
            &target,
            &frame,
            resolved,
            PendingEquality::candidate(c("Bool"), return_guard, c("Bool.true"), return_proof),
            astep.valid().clone(),
        )
        .unwrap();
    let initialization = assem
        .congruence_function(
            initialized.equality().clone(),
            model.config_type(),
            model.run_function(&NatTerm::literal(3)),
        )
        .unwrap();
    let prefix = assem
        .concatenate(cstep.run().clone(), astep.run().clone())
        .unwrap();
    let whole = assem.concatenate(prefix, returned.run().clone()).unwrap();
    // Preserve the original proof term, but expose the definitionally equal
    // run3 endpoint across beta reduction and concatenated literal fuel.
    // Independent final kernel replay must check this conversion as well.
    let initialization = assem
        .convert_endpoints(
            initialization,
            model.run(&NatTerm::literal(3), initialized.equality().left().clone()),
            whole.equality().left().clone(),
        )
        .unwrap();
    let full = assem
        .compose(initialization, whole.equality().clone())
        .unwrap();
    let mut term = full.term().clone();
    for p in ps.iter().rev() {
        term = p.lam(term);
    }
    drop(assem);
    let term = scope.close(&term).unwrap();
    let actual = connection::ir_claim(&subject(
        w,
        &format!(
            "fn addition(x:u64)->u64 {{ x.wrapping_add({}) }}",
            w.literal()
        ),
    ))
    .unwrap();
    let mut tc = TypeChecker::new(env);
    tc.set_allow_unsafe(false);
    tc.set_allow_partial(false);
    tc.check_type(&term, &actual).unwrap();
    assert!(!tc.heartbeat_spent());
    term
}

fn actual_dir() -> std::path::PathBuf { std::env::var_os("TRUST_ACTUAL_THIR_INPUT").unwrap().into() }
fn actual_facts() -> serde_json::Value {
 serde_json::from_slice(&std::fs::read(actual_dir().join("ACTUAL-THIR.json")).unwrap()).unwrap()
}
fn original() -> (String,Vec<u8>,Module) {
 let source=String::from_utf8(std::fs::read(actual_dir().join("original-source.rs")).unwrap()).unwrap();
 let bytes=std::fs::read(actual_dir().join("original-module.bin")).unwrap();
 let module=trust_ir::binary::deserialize_module(&bytes).unwrap();
 assert_eq!(trust_ir::binary::serialize_module(&module).unwrap(),bytes,"exact original producer bytes, no normalization");
 assert!(trust_ir_build::validate_module(&module).is_empty());
 let facts=actual_facts();assert_eq!(facts["closed_profile"]["accepted"],true);
 assert_eq!(facts["signature"],"fn(u64) -> u64");
 assert_eq!(facts["selected_path"],"addition");
 assert_eq!(facts["calls"][0]["selected_primitive_model"],"core-u64-wrapping-add-v1");
 (source,bytes,module)
}
#[test]
fn actual_original_thir_module_source_addition_checked_and_retained() {
 let (source,bytes,module)=original();
 let w=RustU64AdditionModule::from_module(&module,module.functions[0].id,4096).unwrap();
 assert_eq!(w.original_bytes(),bytes);
 let facts=actual_facts();assert_eq!(facts["closed_profile"]["literal"].as_u64(),Some(w.literal()));
 assert_eq!(facts["closed_profile"]["function_name"],w.function_name());
 let expected=subject(&w,&source);let ir=proof(&w);
 let packet=connection::AdditionPacket{subject:expected.clone(),proof:connection::candidate(&expected,ir.clone()).unwrap()};
 let checked=connection::replay(&expected,&packet).unwrap();
 assert_eq!(checked.subject().module_bytes,bytes);
 let dir=std::path::PathBuf::from(std::env::var_os("TRUST_ACTUAL_PROOF_OUT").unwrap());std::fs::create_dir_all(&dir).unwrap();
 for (name,term) in [("ir-proof",ir),("claim",checked.claim().clone()),("proof",checked.proof().clone())] {
  std::fs::write(dir.join(format!("{name}.json")),serde_json::to_vec(&term).unwrap()).unwrap();
 }
 std::fs::write(dir.join("original-module.bin"),bytes).unwrap();
 std::fs::write(dir.join("original-source.rs"),source).unwrap();
}

// Fresh consumer: the original producer/IR proof assembler is forbidden.
fn decode_retained_expr(bytes:&[u8])->Expr {
 use serde::Deserialize;
 assert!(bytes.len()<=8*1024*1024);
 clean_kernel::with_decode_resource_limits(clean_kernel::DecodeResourceLimits{max_nodes:1_000_000,max_depth:512},||{
  let mut de=serde_json::Deserializer::from_slice(bytes);de.disable_recursion_limit();
  let value=Expr::deserialize(&mut de).unwrap();de.end().unwrap();value
 })
}
#[test]
fn fresh_actual_thir_original_proof_and_real_wrong_module_refusal() {
 assert_eq!(std::env::var("TRUST_G4_FORBID_PRODUCER").unwrap(),"1");
 let d=std::path::PathBuf::from(std::env::var_os("TRUST_ACTUAL_RETAINED_PROOF").unwrap());
 let (source,bytes,module)=original();
 let w=RustU64AdditionModule::from_module(&module,module.functions[0].id,4096).unwrap();
 assert_eq!(w.original_bytes(),bytes);
 let expected=subject(&w,&source);
 let original=decode_retained_expr(&std::fs::read(d.join("proof.json")).unwrap());
 let goal=decode_retained_expr(&std::fs::read(d.join("claim.json")).unwrap());
 assert_eq!(connection::claim(&expected).unwrap(),goal);
 let checked=connection::replay(&expected,&connection::AdditionPacket{subject:expected.clone(),proof:original.clone()}).unwrap();
 let zero=std::path::PathBuf::from(std::env::var_os("TRUST_ACTUAL_ZERO_INPUT").unwrap());
 let zero_bytes=std::fs::read(zero.join("original-module.bin")).unwrap();
 let zero_module=trust_ir::binary::deserialize_module(&zero_bytes).unwrap();
 assert_eq!(trust_ir::binary::serialize_module(&zero_module).unwrap(),zero_bytes);
 assert!(trust_ir_build::validate_module(&zero_module).is_empty());
 let zero_w=RustU64AdditionModule::from_module(&zero_module,zero_module.functions[0].id,4096).unwrap();
 assert_eq!(zero_w.literal(),0);
 let zero_source=std::fs::read_to_string(zero.join("original-source.rs")).unwrap();
 let facts:serde_json::Value=serde_json::from_slice(&std::fs::read(zero.join("ACTUAL-THIR.json")).unwrap()).unwrap();
 assert_eq!(facts["closed_profile"]["accepted"],true);
 let mut wrong=subject(&zero_w,&zero_source);wrong.original_instance=facts["owner_hash"].as_str().unwrap().into();
 let refused=connection::replay(&wrong,&connection::AdditionPacket{subject:wrong.clone(),proof:original}).unwrap_err();
 let audit=environment().audit_certification(checked.claim(),checked.proof());assert!(audit.is_certified());
 for name in &audit.dependencies {
  for deps in [environment().axiom_deps(name),environment().foundational_axiom_deps(name),environment().trust_marker_deps(name)] {
   assert!(deps.unwrap().is_empty(),"{name}");
  }
 }
 let out=std::path::PathBuf::from(std::env::var_os("TRUST_ACTUAL_PROOF_OUT").unwrap());std::fs::create_dir_all(&out).unwrap();
 std::fs::write(out.join("fresh-replay.json"),serde_json::to_vec(&serde_json::json!({"producer_forbidden":true,"claim":checked.claim(),"proof":checked.proof(),"original_module_bytes":bytes,"dependencies":audit.dependencies.iter().map(|n|environment().get_const(n).unwrap().clone()).collect::<Vec<_>>(),"wrong_actual_valid_module_literal":zero_w.literal(),"wrong_actual_module_replay_refusal":refused,"scope":"Original source MODEL + actual captured THIR Module data connection only. No core wrapper-body theorem/source-refinement/NoUB/admission/native/physical ABI/proof grade."})).unwrap()).unwrap();
}
