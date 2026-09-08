// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use clean_kernel::Environment;
use trust_certify::clean_island::CleanIslandSession;
use trust_clean_ir_gate::{admit_wrapping_binop, reflect_wrapping_binop};
use trust_clean_origin::{CleanOriginPlan, plan_clean_origin_body};
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{BlockId, FuncId, FuncTyId};
use trust_ir::{BinOp, Block, Function, Inst, Producer};

const PROGRAM: &[(&str, &str)] = &[
    ("add8", "def add8 (a b : UInt8) : UInt8 := a + b"),
    ("sub8", "def sub8 (a b : UInt8) : UInt8 := a - b"),
    ("mul8", "def mul8 (a b : UInt8) : UInt8 := a * b"),
    ("add16", "def add16 (a b : UInt16) : UInt16 := a + b"),
    ("sub16", "def sub16 (a b : UInt16) : UInt16 := a - b"),
    ("mul16", "def mul16 (a b : UInt16) : UInt16 := a * b"),
    ("add32", "def add32 (a b : UInt32) : UInt32 := a + b"),
    ("sub32", "def sub32 (a b : UInt32) : UInt32 := a - b"),
    ("mul32", "def mul32 (a b : UInt32) : UInt32 := a * b"),
    ("add64", "def add64 (a b : UInt64) : UInt64 := a + b"),
    ("sub64", "def sub64 (a b : UInt64) : UInt64 := a - b"),
    ("mul64", "def mul64 (a b : UInt64) : UInt64 := a * b"),
];

fn program_environment() -> Environment {
    let mut session = CleanIslandSession::new();
    for (name, source) in
        PROGRAM.iter().copied().chain([("subLit8", "def subLit8 (a : UInt8) : UInt8 := a - 7")])
    {
        let outcome = session.check(source);
        assert!(!outcome.is_rejected(), "`{name}` must kernel-check: {outcome:?}");
    }
    session.environment().expect("untainted session").clone()
}

fn emitted(env: &Environment, name: &str) -> (CleanOriginPlan, FuncTy, Function) {
    let plan = plan_clean_origin_body(env, name)
        .unwrap_or_else(|refusal| panic!("`{name}` must plan: {refusal:?}"));
    let signature = trust_clean_ir::trust_ir_func_ty(plan.signature())
        .unwrap_or_else(|refusal| panic!("`{name}` signature must lower: {refusal}"));
    let function =
        trust_clean_ir::emit_clean_origin_function(&plan, FuncId::new(0), FuncTyId::new(0))
            .unwrap_or_else(|refusal| panic!("`{name}` must emit: {refusal}"));
    (plan, signature, function)
}

fn mutate_binop(function: &Function, replacement: BinOp) -> Function {
    let mut changed = function.clone();
    for node in &mut changed.blocks[0].body {
        if let Inst::BinOp { op, .. } = &mut node.inst {
            *op = replacement;
            return changed;
        }
    }
    panic!("fixture has no BinOp")
}

fn rewrite_carrier(function: &Function, from: &Ty, to: Ty) -> Function {
    let mut changed = function.clone();
    for (_, ty) in &mut changed.blocks[0].params {
        if ty == from {
            *ty = to.clone();
        }
    }
    for node in &mut changed.blocks[0].body {
        match &mut node.inst {
            Inst::Const { ty, .. } | Inst::BinOp { ty, .. } if ty == from => *ty = to.clone(),
            _ => {}
        }
    }
    changed
}

fn strip_line_comments(source: &str) -> String {
    source
        .lines()
        .map(|line| line.split_once("//").map_or(line, |(code, _)| code))
        .collect::<Vec<_>>()
        .join("\n")
}

fn compact_code(source: &str) -> String {
    strip_line_comments(source).split_whitespace().collect()
}

fn source_between<'a>(source: &'a str, start: &str, end: &str) -> &'a str {
    let (_, tail) = source.split_once(start).unwrap_or_else(|| panic!("missing start `{start}`"));
    let (body, _) = tail.split_once(end).unwrap_or_else(|| panic!("missing end `{end}`"));
    body
}

#[test]
fn all_twelve_operation_width_pairs_mint_and_authenticate() {
    let env = program_environment();
    let mut admitted = Vec::new();
    for (name, _) in PROGRAM {
        let (plan, signature, function) = emitted(&env, name);
        let token = admit_wrapping_binop(&env, &plan, 7, name, &signature, &function)
            .unwrap_or_else(|refusal| panic!("`{name}` gate refused: {}", refusal.note()));
        token
            .authenticate(name, 7, name, &signature, &function)
            .unwrap_or_else(|refusal| panic!("`{name}` token refused: {}", refusal.note()));
        admitted.push((token.carrier_tag(), token.method_tag()));
    }
    assert_eq!(admitted.len(), 12);
    for carrier in ["UInt8", "UInt16", "UInt32", "UInt64"] {
        assert_eq!(admitted.iter().filter(|(tag, _)| *tag == carrier).count(), 3);
    }
    assert!(admitted.iter().all(|(_, method)| *method == "definitional-equality"));
}

#[test]
fn admitted_uint64_add_executes_real_wraparound() {
    let env = program_environment();
    let (plan, signature, function) = emitted(&env, "add64");
    let token = admit_wrapping_binop(&env, &plan, 11, "fixture::add64", &signature, &function)
        .expect("gate admits");
    token
        .authenticate("add64", 11, "fixture::add64", &signature, &function)
        .expect("token authenticates");

    let outcome = Interpreter::new()
        .execute_function(
            &function,
            vec![
                InterpretValue::int(Ty::U64, i128::from(u64::MAX)).expect("max u64"),
                InterpretValue::int(Ty::U64, 1).expect("one"),
            ],
        )
        .expect("emitted TrustIR executes");
    assert_eq!(outcome.returns.len(), 1);
    assert_eq!(
        outcome.returns[0].as_int().expect("integer result").as_unsigned(),
        0,
        "UInt64 addition must wrap at 2^64"
    );
}

#[test]
fn add_to_sub_body_mutation_is_a_kernel_disagreement() {
    let env = program_environment();
    let (plan, signature, function) = emitted(&env, "add8");
    let wrong = mutate_binop(&function, BinOp::Sub);
    let refusal = admit_wrapping_binop(&env, &plan, 3, "fixture::add8", &signature, &wrong)
        .expect_err("mutated operation must not receive a permission");
    assert_eq!(refusal.stage(), "kernel-disagreement", "{}", refusal.note());
}

#[test]
fn noncommutative_sub_operand_swap_is_a_kernel_disagreement() {
    let env = program_environment();
    let (plan, signature, function) = emitted(&env, "sub8");
    admit_wrapping_binop(&env, &plan, 12, "fixture::sub8", &signature, &function)
        .expect("positive Sub fixture must admit");
    let mut swapped = function;
    for node in &mut swapped.blocks[0].body {
        if let Inst::BinOp { lhs, rhs, .. } = &mut node.inst {
            std::mem::swap(lhs, rhs);
            break;
        }
    }
    let refusal = admit_wrapping_binop(&env, &plan, 12, "fixture::sub8", &signature, &swapped)
        .expect_err("Sub operand order is semantic and must be reflected exactly");
    assert_eq!(refusal.stage(), "kernel-disagreement", "{}", refusal.note());
}

#[test]
fn in_range_constant_literal_change_is_a_kernel_disagreement() {
    let env = program_environment();
    let (plan, signature, function) = emitted(&env, "subLit8");
    admit_wrapping_binop(&env, &plan, 13, "fixture::subLit8", &signature, &function)
        .expect("positive literal fixture must admit");
    let mut changed = function;
    let mut found = false;
    for node in &mut changed.blocks[0].body {
        if let Inst::Const { value: trust_ir::Constant::Int(value), .. } = &mut node.inst {
            *value += 1;
            found = true;
            break;
        }
    }
    assert!(found, "fixture must contain a materialized literal");
    let refusal = admit_wrapping_binop(&env, &plan, 13, "fixture::subLit8", &signature, &changed)
        .expect_err("in-range literal mutation must reach and fail the kernel comparison");
    assert_eq!(refusal.stage(), "kernel-disagreement", "{}", refusal.note());
}

#[test]
fn body_mutation_invalidates_an_already_minted_token() {
    let env = program_environment();
    let (plan, signature, function) = emitted(&env, "add8");
    let token = admit_wrapping_binop(&env, &plan, 3, "fixture::add8", &signature, &function)
        .expect("gate admits");
    let wrong = mutate_binop(&function, BinOp::Sub);
    let refusal = token
        .authenticate("add8", 3, "fixture::add8", &signature, &wrong)
        .expect_err("digest-bound token must be stale after mutation");
    assert_eq!(refusal.stage(), "token-digest", "{}", refusal.note());
}

#[test]
fn mixed_link_def_path_mutation_invalidates_the_token() {
    let env = program_environment();
    let (plan, signature, function) = emitted(&env, "add8");
    let token = admit_wrapping_binop(&env, &plan, 3, "m::clean_add8", &signature, &function)
        .expect("gate admits");
    let refusal = token
        .authenticate("add8", 3, "other::clean_add8", &signature, &function)
        .expect_err("permission must bind the Rust-side mixed-link key");
    assert_eq!(refusal.stage(), "token-digest", "{}", refusal.note());
}

#[test]
fn source_definition_index_mutation_invalidates_the_token() {
    let env = program_environment();
    let (plan, signature, function) = emitted(&env, "add8");
    let token = admit_wrapping_binop(&env, &plan, 41, "m::clean_add8", &signature, &function)
        .expect("gate admits");
    let refusal = token
        .authenticate("add8", 42, "m::clean_add8", &signature, &function)
        .expect_err("permission must bind the source definition index");
    assert_eq!(refusal.stage(), "token-digest", "{}", refusal.note());
}

#[test]
fn final_publication_rebinds_only_identity_fields_and_digests_exact_final_function() {
    let env = program_environment();
    let (plan, signature, function) = emitted(&env, "mul32");
    let token = admit_wrapping_binop(&env, &plan, 17, "m::clean_mul32", &signature, &function)
        .expect("gate admits");
    let preappend_digest = token.subject_digest();

    let mut published = function.clone();
    published.producer = Some(Producer::Clean);
    let baseline = token
        .authenticate_published("mul32", 17, "m::clean_mul32", &signature, &function, &published)
        .expect("the exact append relocation must authenticate");
    assert_ne!(
        baseline.subject_digest(),
        preappend_digest,
        "producer-stamped final Function must not disclose the placeholder digest"
    );
    assert_eq!(baseline.carrier_tag(), "UInt32");

    let mut changed_id = published.clone();
    changed_id.id = FuncId::new(23);
    let changed_id_auth = token
        .authenticate_published("mul32", 17, "m::clean_mul32", &signature, &function, &changed_id)
        .expect("FuncId-only relocation authenticates");
    assert_ne!(
        changed_id_auth.subject_digest(),
        baseline.subject_digest(),
        "final subject hash must have independent FuncId teeth"
    );

    let mut changed_ty = published.clone();
    changed_ty.ty = FuncTyId::new(9);
    let changed_ty_auth = token
        .authenticate_published("mul32", 17, "m::clean_mul32", &signature, &function, &changed_ty)
        .expect("FuncTyId-only relocation authenticates");
    assert_ne!(
        changed_ty_auth.subject_digest(),
        baseline.subject_digest(),
        "final subject hash must have independent FuncTyId teeth"
    );

    let mut wrong_producer = function.clone();
    wrong_producer.producer = Some(Producer::TRust);
    let refusal = token
        .authenticate_published(
            "mul32",
            17,
            "m::clean_mul32",
            &signature,
            &function,
            &wrong_producer,
        )
        .expect_err("a published target must carry the Clean producer stamp");
    assert_eq!(refusal.stage(), "published-producer", "{}", refusal.note());

    let mut forbidden = published;
    forbidden.name.push_str("_retargeted");
    let refusal = token
        .authenticate_published("mul32", 17, "m::clean_mul32", &signature, &function, &forbidden)
        .expect_err("publication may not mutate any other Function field");
    assert_eq!(refusal.stage(), "published-relocation", "{}", refusal.note());
}

#[test]
fn source_uint64_to_trustir_uint32_width_skew_is_refused() {
    let env = program_environment();
    let (plan, signature, function) = emitted(&env, "add64");
    let skewed_signature =
        FuncTy { params: vec![Ty::U32, Ty::U32], returns: vec![Ty::U32], is_vararg: false };
    let skewed_function = rewrite_carrier(&function, &Ty::U64, Ty::U32);
    let refusal =
        admit_wrapping_binop(&env, &plan, 9, "fixture::add64", &skewed_signature, &skewed_function)
            .expect_err("carrier width skew must refuse");
    assert_eq!(refusal.stage(), "source-ir-carrier", "{}", refusal.note());
    assert_ne!(signature, skewed_signature);
}

#[test]
fn source_to_trustir_parameter_arity_skew_is_refused_directly() {
    let env = program_environment();
    let (plan, mut signature, function) = emitted(&env, "add16");
    signature.params.pop();
    let refusal = admit_wrapping_binop(&env, &plan, 5, "fixture::add16", &signature, &function)
        .expect_err("source and TrustIR parameter counts must agree exactly");
    assert_eq!(refusal.stage(), "source-ir-arity", "{}", refusal.note());
}

#[test]
fn division_and_shift_are_outside_the_closed_operation_table() {
    let env = program_environment();
    let (_plan, signature, function) = emitted(&env, "add32");
    for unsupported in [BinOp::UDiv, BinOp::Shl] {
        let wrong = mutate_binop(&function, unsupported);
        let refusal = reflect_wrapping_binop(&signature, &wrong)
            .expect_err("unsupported operation must refuse before the kernel");
        assert_eq!(refusal.stage(), "binop", "{}", refusal.note());
    }
}

#[test]
fn signed_and_bitvector_like_ir_carriers_are_not_admitted_by_this_slice() {
    let env = program_environment();
    let (_plan, _signature, function) = emitted(&env, "add64");
    let signed_signature =
        FuncTy { params: vec![Ty::I64, Ty::I64], returns: vec![Ty::I64], is_vararg: false };
    let signed_function = rewrite_carrier(&function, &Ty::U64, Ty::I64);
    let refusal = reflect_wrapping_binop(&signed_signature, &signed_function)
        .expect_err("I64 is not a UInt64 carrier");
    assert_eq!(refusal.stage(), "ir-carrier", "{}", refusal.note());
}

#[test]
fn malformed_control_flow_and_code_after_return_are_refused() {
    let env = program_environment();
    let (_plan, signature, function) = emitted(&env, "mul16");

    let mut two_blocks = function.clone();
    two_blocks.blocks.push(Block::new(BlockId::new(1)));
    let refusal = reflect_wrapping_binop(&signature, &two_blocks)
        .expect_err("second block is outside straight-line slice");
    assert_eq!(refusal.stage(), "control-flow", "{}", refusal.note());

    let mut after_return = function.clone();
    let extra = after_return.blocks[0].body[0].clone();
    after_return.blocks[0].body.push(extra);
    let refusal = reflect_wrapping_binop(&signature, &after_return)
        .expect_err("instruction after Return must refuse");
    assert_eq!(refusal.stage(), "control-flow", "{}", refusal.note());
}

#[test]
fn production_collector_pins_both_targeted_precursor_refusals_to_fatal_helper() {
    let source = include_str!("../../../compiler/rustc_mir_transform/src/clean_origin_ir.rs");
    let code = strip_line_comments(source);
    assert_eq!(
        code.matches("fn trust_ir_precursor_refusal(").count(),
        1,
        "one fail-closed policy helper owns the bounded exception"
    );
    assert_eq!(
        code.matches("trust_ir_precursor_refusal(").count(),
        3,
        "signature Err + Function-emission Err must both call the helper"
    );
    for stage in ["\"signature-lowering\"", "\"function-emission\""] {
        assert!(code.contains(stage), "missing source-pinned precursor stage {stage}");
    }
    let helper = strip_line_comments(source_between(
        source,
        "fn trust_ir_precursor_refusal(",
        "fn shape_tag(",
    ));
    assert!(helper.contains("CleanOriginShape::WrappingBinOp"));
    assert!(helper.contains("span_fatal"));
    assert!(helper.contains("never recorded"));
    assert!(helper.contains("general lane"));
}

#[test]
fn production_collector_mints_and_carries_the_exact_private_gate_subject() {
    let source = include_str!("../../../compiler/rustc_mir_transform/src/clean_origin_ir.rs");
    let collector = compact_code(source_between(
        source,
        "pub fn collect_clean_origin_ir(",
        "fn trust_ir_precursor_refusal(",
    ));
    assert!(
        collector.contains(
            "trust_clean_ir_gate::admit_wrapping_binop(env,&plan,def_index,&def_path,&signature,&function,)"
        ),
        "collector must mint over the exact source identity, signature, and emitted Function"
    );
    assert!(
        collector.contains(
            "CleanOriginIrRecord{def_index,def_path,clean_name:name,shape,signature,function,gate,tv,tv_note,}"
        ),
        "the minted private gate must travel in the exact emitted record"
    );
}

#[test]
fn production_source_and_kernel_carrier_belts_are_comment_stripped_and_pinned() {
    let source = include_str!("../src/lib.rs");
    let source_belt = strip_line_comments(source_between(
        source,
        "fn source_signature_carrier(",
        "fn ir_signature_carrier(",
    ));
    for tooth in [
        "signature.hypotheses()",
        "signature.preconditions()",
        "signature.arguments().iter()",
        "argument.rust()",
        "signature.result().rust()",
        "carrier.rust_ty()",
    ] {
        assert!(source_belt.contains(tooth), "missing source carrier tooth `{tooth}`");
    }

    let admit_belt = strip_line_comments(source_between(
        source,
        "pub fn admit_wrapping_binop(",
        "pub fn reflect_wrapping_binop(",
    ));
    for tooth in [
        "plan.signature().arguments().len() != signature.params.len()",
        "faithful.admitted_at() != &expected_rust",
        "FaithfulnessMethod::DefinitionalEquality",
    ] {
        assert!(admit_belt.contains(tooth), "missing admission carrier tooth `{tooth}`");
    }
}

#[test]
fn append_wiring_discloses_only_the_authenticated_final_subject() {
    let source = include_str!("../../trust-thir-lower/src/clean_origin_join.rs");
    let append = strip_line_comments(source_between(
        source,
        "pub fn append_clean_origin(",
        "fn merge_general_module(",
    ));
    assert!(
        !append.contains("gate.subject_digest()"),
        "append must never disclose the placeholder token digest"
    );
    let publication =
        source_between(&append, "let (ty, insert_ty)", "module.functions.push(function);");
    let compact_publication: String = publication.split_whitespace().collect();
    let exact_auth = "gate.authenticate_published(&record.clean_name,record.def_index,&record.def_path,&record.signature,&record.function,&function,)";
    let authenticate = compact_publication
        .find(exact_auth)
        .expect("final authentication must bind all six exact source/final subject arguments");
    let compact_digest = compact_publication
        .find("published.subject_digest()")
        .expect("compacted publication retains final digest accessor");
    assert!(authenticate < compact_digest, "digest accessor must follow final authentication");
    assert!(publication.contains("function.id = id;"));
    assert!(publication.contains("function.ty = ty;"));
    assert!(publication.contains("function.producer = Some(Producer::Clean);"));

    // From candidate construction to push, the only permitted references to
    // the mutable local are the three final placement assignments and the
    // exact original/final authentication arguments above. Any later read,
    // alias, or mutation adds another identifier and trips this pin before a
    // stale digest can be paired with a changed body.
    let candidate_to_push = strip_line_comments(source_between(
        &append,
        "let mut function = record.function.clone();",
        "module.functions.push(function);",
    ));
    let function_references = candidate_to_push
        .split(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '_'))
        .filter(|identifier| *identifier == "function")
        .count();
    assert_eq!(
        function_references, 5,
        "only three placement writes plus the original/final authentication arguments are allowed"
    );

    let after_push = compact_code(source_between(
        &append,
        "module.functions.push(function);",
        "install_disclosure(module, &summary);",
    ));
    assert!(
        after_push.contains(
            "summary.emitted.push(EmittedRow{def_index:record.def_index,def_path:record.def_path,clean_name:record.clean_name,shape:record.shape,func_id:id.index(),tier,gate_subject_digest,gate_carrier,gate_method,tv_note,})"
        ),
        "the exact final-auth digest tuple must be carried into the emitted disclosure row"
    );
}
