// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use clean_kernel::Environment;
use trust_certify::clean_island::CleanIslandSession;
use trust_clean_ir_gate::{
    GatedShape, admit_clean_origin, admit_wrapping_binop, gate_targets, reflect_gated,
    reflect_wrapping_binop,
};
use trust_clean_origin::{CleanOriginPlan, check_faithful, plan_clean_origin_body};
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

/// The W2 gate-widening targets (projection / constant-uint at exact UInt
/// carriers) plus two NON-targets at carriers the gate has no reflector for.
const GATED_EXTRA: &[(&str, &str, Option<GatedShape>)] = &[
    ("fst8", "def fst8 (a b : UInt8) : UInt8 := a", Some(GatedShape::Projection { projected: 0 })),
    (
        "snd16",
        "def snd16 (a b : UInt16) : UInt16 := b",
        Some(GatedShape::Projection { projected: 1 }),
    ),
    ("id32", "def id32 (a : UInt32) : UInt32 := a", Some(GatedShape::Projection { projected: 0 })),
    (
        "snd64",
        "def snd64 (a b : UInt64) : UInt64 := b",
        Some(GatedShape::Projection { projected: 1 }),
    ),
    ("k8", "def k8 : UInt8 := 7", Some(GatedShape::ConstantUint { value: 7 })),
    ("k16", "def k16 (a : UInt16) : UInt16 := 300", Some(GatedShape::ConstantUint { value: 300 })),
    (
        "k64",
        "def k64 (a b : UInt64) : UInt64 := 4294967296",
        Some(GatedShape::ConstantUint { value: 4_294_967_296 }),
    ),
    // Non-targets: emittable projections at carriers this gate has no
    // reflector for. (A `Bool` LITERAL is not a numeral and never plans at all.)
    ("natId", "def natId (a : Nat) : Nat := a", None),
    ("boolId", "def boolId (a : Bool) : Bool := a", None),
];

fn program_environment() -> Environment {
    let mut session = CleanIslandSession::new();
    for (name, source) in PROGRAM
        .iter()
        .copied()
        .chain([("subLit8", "def subLit8 (a : UInt8) : UInt8 := a - 7")])
        .chain(GATED_EXTRA.iter().map(|(name, source, _)| (*name, *source)))
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
    let mut function =
        trust_clean_ir::emit_clean_origin_function(&plan, FuncId::new(0), FuncTyId::new(0))
            .unwrap_or_else(|refusal| panic!("`{name}` must emit: {refusal}"));
    // WS5.2: the collector names the subject by the minted Rust item's link-time symbol and
    // moves the Lean spelling to `display_path` before minting; the fixture does the same with a
    // fixture symbol (this crate has no `tcx`, and the gate does not compute the symbol).
    bind_fixture_link_symbol(&mut function);
    (plan, signature, function)
}

/// The collector's WS5.2 binding, over a deterministic fixture symbol.
fn bind_fixture_link_symbol(function: &mut Function) {
    assert!(function.display_path.is_none(), "the emitter leaves display_path to the binder");
    let symbol = format!("_RNvCs0_7fixture{}", function.name.len());
    let lean = std::mem::replace(&mut function.name, symbol);
    function.name.push_str(&lean.replace('.', "_"));
    function.display_path = Some(lean);
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

/// Index one past the string literal whose opening quote is at `open`.
fn literal_end(code: &str, open: usize) -> usize {
    let bytes = code.as_bytes();
    let mut index = open + 1;
    while index < bytes.len() {
        match bytes[index] {
            b'\\' => index += 2,
            b'"' => return index + 1,
            _ => index += 1,
        }
    }
    panic!("unterminated string literal at byte {open}");
}

/// Index one past the delimiter closing the `{…}` or `(…)` group that opens at
/// `open`. String literals are skipped, so the braces of `format!` text cannot
/// unbalance the walk.
fn group_end(code: &str, open: usize) -> usize {
    let bytes = code.as_bytes();
    let (left, right) = match bytes[open] {
        b'{' => (b'{', b'}'),
        b'(' => (b'(', b')'),
        other => panic!("a group opens with `{{` or `(`, not `{}`", other as char),
    };
    let (mut depth, mut index) = (0usize, open);
    while index < bytes.len() {
        match bytes[index] {
            b'"' => {
                index = literal_end(code, index);
                continue;
            }
            byte if byte == left => depth += 1,
            byte if byte == right => {
                depth -= 1;
                if depth == 0 {
                    return index + 1;
                }
            }
            _ => {}
        }
        index += 1;
    }
    panic!("unbalanced group opening at byte {open}");
}

/// The body of the `Err(<binding>)` arm of the one `match <callee>(…) { … }` in
/// compacted `code`. The arm is found at the match block's OWN top level, so the
/// `Err` arm of a nested match can never stand in for it.
fn match_err_arm<'a>(code: &'a str, callee: &str, binding: &str) -> &'a str {
    let head = format!("match{callee}(");
    assert_eq!(code.matches(&head).count(), 1, "exactly one `match {callee}(…)`");
    let scrutinee = code.find(&head).expect("counted above") + head.len() - 1;
    let open = group_end(code, scrutinee);
    assert_eq!(code.as_bytes()[open], b'{', "`match {callee}(…)` must open its arms next");
    let block = &code[open + 1..group_end(code, open) - 1];
    let arm = format!("Err({binding})=>{{");
    let (bytes, mut index) = (block.as_bytes(), 0);
    while index < bytes.len() {
        if block[index..].starts_with(&arm) {
            let body = index + arm.len() - 1;
            return &block[body + 1..group_end(block, body) - 1];
        }
        index = match bytes[index] {
            b'{' | b'(' => group_end(block, index),
            b'"' => literal_end(block, index),
            _ => index + 1,
        };
    }
    panic!("`match {callee}(…)` has no top-level `Err({binding})` arm");
}

/// `arm` routes its refusal through the fail-closed helper at `stage` BEFORE any
/// skip is recorded, and records exactly what the helper returned.
fn assert_arm_calls_precursor_helper(arm: &str, stage: &str) {
    let call = "trust_ir_precursor_refusal(";
    assert_eq!(arm.matches(call).count(), 1, "the `{stage}` Err arm must call the helper once");
    let at = arm.find(call).expect("counted above");
    let args = &arm[at + call.len() - 1..group_end(arm, at + call.len() - 1)];
    let stage_literal = format!("\"{}\"", stage.split_whitespace().collect::<String>());
    assert!(args.contains(&stage_literal), "helper call must name stage `{stage}`: {args}");
    assert!(arm[..at].ends_with("letreason="), "the `{stage}` arm must record the helper's return");
    let skipped = arm.find("CleanOriginIrOutcome::Skipped(").expect("the arm records a skip");
    assert!(at < skipped, "the `{stage}` helper must run before the skip is recorded");
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

/// WS5.2 NEGATIVE TWINS. The subject is bound to the plan through its DISPLAY
/// PATH (the Lean spelling) and named by the Rust item's link-time symbol; a
/// subject still carrying the Lean spelling as its NAME was never bound, and one
/// whose display path names another declaration is a different subject. Both
/// are refused at `subject-name` — the plan binding moved fields, it did not
/// weaken.
#[test]
fn an_unbound_or_misbound_subject_is_refused_at_subject_name() {
    let env = program_environment();
    let (plan, signature, bound) = emitted(&env, "add64");
    admit_wrapping_binop(&env, &plan, 11, "fixture::add64", &signature, &bound)
        .expect("the bound subject mints (positive control)");

    let mut unbound = bound.clone();
    unbound.name = bound.display_path.clone().expect("bound subjects carry the Lean spelling");
    unbound.display_path = None;
    let refusal = admit_wrapping_binop(&env, &plan, 11, "fixture::add64", &signature, &unbound)
        .expect_err("a subject named by its Lean spelling was never bound to a link symbol");
    assert_eq!(refusal.stage(), "subject-name", "{}", refusal.note());

    let mut misbound = bound.clone();
    misbound.display_path = Some("sub64".to_string());
    let refusal = admit_wrapping_binop(&env, &plan, 11, "fixture::add64", &signature, &misbound)
        .expect_err("a display path naming another declaration is another subject");
    assert_eq!(refusal.stage(), "subject-name", "{}", refusal.note());

    let mut lean_named = bound.clone();
    lean_named.name = "add64".to_string();
    let refusal = admit_wrapping_binop(&env, &plan, 11, "fixture::add64", &signature, &lean_named)
        .expect_err("MUTATION CONTROL: a name equal to the Lean spelling is not a bound symbol");
    assert_eq!(refusal.stage(), "subject-name", "{}", refusal.note());
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
    let skewed_signature = FuncTy {
        params: vec![Ty::U32, Ty::U32],
        returns: vec![Ty::U32],
        is_vararg: false,
        abi: None,
    };
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
    let signed_signature = FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
        abi: None,
    };
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
    // The targeted Err arms, located structurally: signature Err + Function-emission
    // Err must both call the helper.
    let collector = compact_code(source_between(
        source,
        "pub fn collect_clean_origin_ir(",
        "fn trust_ir_precursor_refusal(",
    ));
    let signature = match_err_arm(&collector, "trust_clean_ir::trust_ir_func_ty", "refusal");
    assert_arm_calls_precursor_helper(signature, "signature-lowering");
    let emission =
        match_err_arm(&collector, "trust_clean_ir::emit_clean_origin_function", "refusal");
    assert_arm_calls_precursor_helper(emission, "function-emission");
    // The third call site is the Rust-call identity-collection Err arm that 7ff041fcf6
    // (2026-09-15, "feat(clean-ir): record sealed Rust calls in the owning module") routed
    // through the same helper. `RustCallChain` is not a gate target today, so the helper
    // returns the reason unchanged there; routing it anyway keeps the refusal fatal if
    // that shape is ever gated.
    let rust_calls = match_err_arm(&collector, "collect_rust_call_callees", "reason");
    assert_arm_calls_precursor_helper(rust_calls, "Rust-call identity collection");
    // WS5.2: the two link-symbol stages — computing the minted Rust item's symbol, and
    // binding it onto the emitted Function before the gate mints. The binding is an
    // `if let Err(reason) = …` rather than a `match`, so its body is located the same
    // structural way: the group that opens right after the call's argument list.
    let symbol = match_err_arm(
        &collector,
        "trust_thir_lower::link_symbol::definition_link_symbol",
        "reason",
    );
    assert_arm_calls_precursor_helper(symbol, "link-symbol");
    let bind_head =
        "ifletErr(reason)=trust_thir_lower::link_symbol::bind_clean_origin_link_symbol(";
    assert_eq!(collector.matches(bind_head).count(), 1, "exactly one link-symbol binding");
    let arguments = collector.find(bind_head).expect("counted above") + bind_head.len() - 1;
    let body = group_end(&collector, arguments);
    assert_eq!(collector.as_bytes()[body], b'{', "the binding's Err body must follow its call");
    let bind = &collector[body + 1..group_end(&collector, body) - 1];
    assert_arm_calls_precursor_helper(bind, "link-symbol");
    // Call sites, the definition excluded: the five named above and no others. A new
    // site must be named here, never silently absorbed into the count.
    assert_eq!(
        code.matches("trust_ir_precursor_refusal(").count()
            - code.matches("fn trust_ir_precursor_refusal(").count(),
        5,
        "helper call sites: signature Err, Function-emission Err, Rust-call collection Err, \
         and the two link-symbol Errs"
    );
    let helper = strip_line_comments(source_between(
        source,
        "fn trust_ir_precursor_refusal(",
        "fn shape_tag(",
    ));
    assert!(helper.contains("gate_targets(plan)"));
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
            "trust_clean_ir_gate::admit_clean_origin(env,&plan,def_index,&def_path,&signature,&function,)"
        ),
        "collector must mint over the exact source identity, signature, and emitted Function"
    );
    // Plan step 3.5: the record also states what the recorder did with the def's MIR body
    // (`mir_gate`, disclosure only), after every field the gate binds.
    assert!(
        collector.contains(
            "CleanOriginIrRecord{def_index,def_path,clean_name:name,shape,gate_target,signature,function,gate,gate_environment,tv,tv_note,mir_gate,}"
        ),
        "the minted private gate must travel in the exact emitted record"
    );
    // Plan step 3.4 (design §4.2): the record names the environment the verdict comes from,
    // for exactly the targeted rows, from the same environment and declaration the gate read.
    assert!(
        collector.contains(
            "letgate_environment=gate_target.then(||{trust_clean_ir_gate::GateEnvironment::of(env,plan.declaration())"
        ),
        "the collector names the targeted row's environment beside its token"
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
        "pub fn admit_clean_origin(",
        "pub fn admit_wrapping_binop(",
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
        source_between(&append, "let (ty, insert_ty)", "publish_clean_row(module, function)");
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
    // Plan step 3.4 (D37 part 1): a targeted row's carrier stamp, written before the final
    // authentication so the published digest binds it.
    let compact_stamp =
        "iftargeted{function.body_gate=Some(trust_clean_ir_gate::clean_carrier_gate_stamp());}";
    let stamp = compact_publication.find(compact_stamp).expect("the carrier stamp is written once");
    assert!(stamp < authenticate, "the stamp must precede the final authentication");

    // From candidate construction to push, the only permitted references to
    // the mutable local are the three final placement assignments, the
    // targeted row's carrier stamp, and the exact original/final
    // authentication arguments above. Any later read, alias, or mutation adds
    // another identifier and trips this pin before a stale digest can be
    // paired with a changed body.
    let candidate_to_push = strip_line_comments(source_between(
        &append,
        "let mut function = record.function.clone();",
        "publish_clean_row(module, function)",
    ));
    let function_references = candidate_to_push
        .split(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '_'))
        .filter(|identifier| *identifier == "function")
        .count();
    assert_eq!(
        function_references, 6,
        "only three placement writes, the carrier stamp, and the original/final authentication \
         arguments are allowed"
    );

    let after_push = compact_code(source_between(
        &append,
        "publish_clean_row(module, function)",
        "install_disclosure(module, &summary);",
    ));
    assert!(
        after_push.contains(
            "summary.emitted.push(EmittedRow{def_index:record.def_index,def_path:record.def_path,clean_name:record.clean_name,shape:record.shape,func_id:id.index(),tier,gate_subject_digest,gate_carrier,gate_method,gate_environment_digest,gate_kernel_version,gate_ledger_digest,tv_note,})"
        ),
        "the exact final-auth digest tuple must be carried into the emitted disclosure row"
    );
}

// ── W2 gate widening: projection and constant-uint ──────────────────────────

#[test]
fn projections_and_constants_mint_and_authenticate_at_their_read_shape() {
    let env = program_environment();
    let mut admitted = 0;
    for (name, _, expected) in GATED_EXTRA {
        let Some(expected) = expected else { continue };
        let (plan, signature, function) = emitted(&env, name);
        assert!(gate_targets(&plan), "`{name}` must be a carrier-gate target");
        let token = admit_clean_origin(&env, &plan, 13, name, &signature, &function)
            .unwrap_or_else(|refusal| panic!("`{name}` gate refused: {}", refusal.note()));
        assert_eq!(token.shape(), *expected, "`{name}` reflected at the wrong shape");
        assert_eq!(token.method_tag(), "definitional-equality");
        token
            .authenticate(name, 13, name, &signature, &function)
            .unwrap_or_else(|refusal| panic!("`{name}` token refused: {}", refusal.note()));
        // The historical wrapping-binop entry point stays exactly as narrow.
        let refusal = admit_wrapping_binop(&env, &plan, 13, name, &signature, &function)
            .expect_err("the wrapping-binop wrapper admits only WrappingBinOp plans");
        assert_eq!(refusal.stage(), "target-shape", "{}", refusal.note());
        admitted += 1;
    }
    assert_eq!(admitted, 7);
}

#[test]
fn non_uint_projection_and_constant_plans_are_not_targeted() {
    let env = program_environment();
    for (name, _, expected) in GATED_EXTRA {
        if expected.is_some() {
            continue;
        }
        let plan = plan_clean_origin_body(&env, name)
            .unwrap_or_else(|refusal| panic!("`{name}` must plan: {refusal:?}"));
        assert!(!gate_targets(&plan), "`{name}` at a non-UInt carrier must not be targeted");
    }
    // A wrapping-binop plan stays targeted unconditionally (the landed contract).
    let (plan, _, _) = emitted(&env, "add8");
    assert!(gate_targets(&plan));
}

#[test]
fn returned_parameter_mutation_is_a_plan_disagreement_and_a_kernel_disagreement() {
    let env = program_environment();
    let (plan, signature, function) = emitted(&env, "fst8");
    let mut wrong = function.clone();
    let other = wrong.blocks[0].params[1].0;
    for node in &mut wrong.blocks[0].body {
        if let Inst::Return { values } = &mut node.inst {
            *values = vec![other];
        }
    }
    // Body-only reflection reads the mutated shape honestly ...
    let reflected = reflect_gated(&signature, &wrong).expect("a projection of the other param");
    assert_eq!(reflected.shape(), GatedShape::Projection { projected: 1 });
    // ... the plan/body belt refuses it before the kernel ...
    let refusal = admit_clean_origin(&env, &plan, 2, "fixture::fst8", &signature, &wrong)
        .expect_err("plan says projected 0, body returns parameter 1");
    assert_eq!(refusal.stage(), "plan-shape", "{}", refusal.note());
    // ... and the kernel itself would refuse the reflected term anyway.
    check_faithful(&env, plan.name(), reflected.term(), plan.result_carrier())
        .expect_err("`fun a b => b` is not definitionally `fst8`");
}

#[test]
fn constant_value_mutation_is_a_plan_disagreement_and_a_kernel_disagreement() {
    let env = program_environment();
    let (plan, signature, function) = emitted(&env, "k16");
    let mut wrong = function.clone();
    for node in &mut wrong.blocks[0].body {
        if let Inst::Const { value, .. } = &mut node.inst {
            *value = trust_ir::Constant::Int(301);
        }
    }
    let reflected = reflect_gated(&signature, &wrong).expect("a constant body");
    assert_eq!(reflected.shape(), GatedShape::ConstantUint { value: 301 });
    let refusal = admit_clean_origin(&env, &plan, 3, "fixture::k16", &signature, &wrong)
        .expect_err("plan says 300, body returns 301");
    assert_eq!(refusal.stage(), "plan-shape", "{}", refusal.note());
    check_faithful(&env, plan.name(), reflected.term(), plan.result_carrier())
        .expect_err("`fun a => 301` is not definitionally `k16`");
}

#[test]
fn a_const_that_does_not_feed_the_return_is_a_shape_refusal() {
    let env = program_environment();
    let (_plan, signature, function) = emitted(&env, "k16");
    // Const present, but the parameter is returned instead.
    let mut dangling = function.clone();
    let param = dangling.blocks[0].params[0].0;
    for node in &mut dangling.blocks[0].body {
        if let Inst::Return { values } = &mut node.inst {
            *values = vec![param];
        }
    }
    let refusal = reflect_gated(&signature, &dangling).expect_err("dangling Const must refuse");
    assert_eq!(refusal.stage(), "shape", "{}", refusal.note());
    // Two Consts, only one returned.
    let mut two = function.clone();
    let extra = two.blocks[0].body[0].clone();
    two.blocks[0].body.insert(0, extra);
    let refusal = reflect_gated(&signature, &two).expect_err("second Const must refuse");
    assert!(refusal.stage() == "shape" || refusal.stage() == "ssa", "{}", refusal.note());
}

#[test]
fn plan_and_body_shape_disagreement_is_refused_before_the_kernel() {
    let env = program_environment();
    let (plan, signature, function) = emitted(&env, "fst8");
    // Same signature, but the body returns a fresh constant: reflects as a
    // constant-uint, while the sealed plan is a projection.
    let mut constant_body = function.clone();
    let konst = trust_ir::value::ValueId::new(9);
    constant_body.blocks[0].body = vec![
        trust_ir::node::InstrNode::new(Inst::Const {
            ty: Ty::U8,
            value: trust_ir::Constant::Int(7),
        })
        .with_result(konst),
        trust_ir::node::InstrNode::new(Inst::Return { values: vec![konst] }),
    ];
    let reflected = reflect_gated(&signature, &constant_body).expect("a constant body");
    assert_eq!(reflected.shape(), GatedShape::ConstantUint { value: 7 });
    let refusal = admit_clean_origin(&env, &plan, 4, "fixture::fst8", &signature, &constant_body)
        .expect_err("a projection plan must not accept a constant body");
    assert_eq!(refusal.stage(), "plan-shape", "{}", refusal.note());
    // And the wrapping-binop reflector keeps its historical refusal for it.
    let refusal = reflect_wrapping_binop(&signature, &constant_body).expect_err("no BinOp");
    assert_eq!(refusal.stage(), "shape", "{}", refusal.note());
}

#[test]
fn a_published_projection_rebinds_only_identity_fields() {
    let env = program_environment();
    let (plan, signature, function) = emitted(&env, "snd64");
    let token =
        admit_clean_origin(&env, &plan, 5, "m::snd64", &signature, &function).expect("gate admits");
    let mut published = function.clone();
    published.id = FuncId::new(17);
    published.ty = FuncTyId::new(3);
    published.producer = Some(Producer::Clean);
    let sealed = token
        .authenticate_published("snd64", 5, "m::snd64", &signature, &function, &published)
        .expect("relocation of id/ty/producer only");
    assert_eq!(sealed.shape(), GatedShape::Projection { projected: 1 });
    assert_ne!(sealed.subject_digest(), token.subject_digest());
    let mut tampered = published.clone();
    tampered.blocks[0].body.rotate_left(0);
    tampered.name.push('!');
    token
        .authenticate_published("snd64", 5, "m::snd64", &signature, &function, &tampered)
        .expect_err("a renamed published subject is a forbidden relocation");
}
