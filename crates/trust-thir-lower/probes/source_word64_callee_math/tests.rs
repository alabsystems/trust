use clean_kernel::{Environment, Expr, KernelTypeError, Level, TypeChecker};
use clean_reflect::{denote_function, tv_anchor_environment, tv_proof_term, tv_statement};
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};
use trust_ir::{CallingConv, Module, Producer, Ty};

#[derive(Serialize, Deserialize)]
struct Packet {
    module_bytes: Vec<u8>,
    proof: Expr,
}

fn captures() -> PathBuf {
    std::env::var_os("TRUST_RUST_CALLEE_CAPTURES").expect("original compiler captures").into()
}

fn output() -> PathBuf {
    std::env::var_os("TRUST_RUST_CALLEE_MATH_OUT").expect("fresh owned output directory").into()
}

fn original(case: &str) -> (Vec<u8>, Module) {
    let directory = captures().join(case).join("capture");
    let facts: serde_json::Value = serde_json::from_slice(
        &std::fs::read(directory.join("ACTUAL-THIR.json")).unwrap()).unwrap();
    let calls: Vec<_> = facts["calls"].as_array().unwrap().iter()
        .filter_map(|call| call.get("retained_entry"))
        .filter(|entry| entry["retained"] == true).collect();
    assert_eq!(calls.len(), 1, "one actual captured metadata owner");
    let bytes = std::fs::read(directory.join(calls[0]["decoded_module"].as_str().unwrap())).unwrap();
    let module = trust_ir::binary::deserialize_module(&bytes).unwrap();
    assert_eq!(trust_ir::binary::serialize_module(&module).unwrap(), bytes,
               "original full metadata module, no normalization or synthesized body");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    assert_eq!(module.functions.len(), 1);
    let function = &module.functions[0];
    assert!(!function.is_declaration());
    assert_eq!(function.producer, Some(Producer::TRust));
    assert_eq!(function.calling_conv, CallingConv::Rust);
    (bytes, module)
}

fn goal(module: &Module, width: u32, duplicate_second: bool) -> Expr {
    let function = &module.functions[0];
    let signature = module.func_type(function.ty).unwrap();
    let ty = match width { 64 => Ty::U64, 32 => Ty::U32, _ => panic!("closed width scope") };
    assert_eq!(signature.params, [ty.clone(), ty.clone()]);
    assert_eq!(signature.returns, [ty]);
    let actual = denote_function(module, function).unwrap();
    assert_eq!((actual.arity, actual.width), (2, width));
    assert!(actual.callees.is_empty(), "no arbitrary callee interpretation");
    let rhs = Expr::apps(Expr::const_str("Nat.mod"), [
        Expr::apps(Expr::const_str("Nat.add"), [Expr::bvar(1),
            Expr::bvar(if duplicate_second { 1 } else { 0 })]),
        Expr::nat_lit_u128(1u128 << width),
    ]);
    tv_statement(&[], 2, &actual.body, &rhs)
}

fn check(env: &Environment, proof: &Expr, claim: &Expr) -> Result<(), KernelTypeError> {
    assert!(!proof.has_fvar_quick() && !proof.has_loose_bvars());
    let mut checker = TypeChecker::new(env);
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.check_type(claim, &Expr::sort(Level::zero()))
        .expect("reconstructed proposition itself must be well typed");
    let result = checker.check_type(proof, claim);
    assert!(!checker.heartbeat_spent());
    assert!(!clean_kernel::tc::declaration_budget_exhausted());
    result
}

fn audit(env: &Environment, proof: &Expr, claim: &Expr) {
    let audit = env.audit_certification(claim, proof);
    assert!(audit.is_certified(), "{audit:?}");
    for name in audit.dependencies {
        assert!(env.axiom_deps(&name).unwrap().is_empty(), "{name}");
        assert!(env.foundational_axiom_deps(&name).unwrap().is_empty(), "{name}");
        assert!(env.trust_marker_deps(&name).unwrap().is_empty(), "{name}");
    }
}

fn produce(module: &Module) -> Expr {
    assert!(std::env::var_os("TRUST_RUST_CALLEE_FORBID_PRODUCER").is_none(),
            "proof production is forbidden in the independent fresh replay");
    let actual = denote_function(module, &module.functions[0]).unwrap();
    tv_proof_term(&[], 2, &actual.body)
}

fn read_packet(path: &Path) -> Packet {
    let bytes = std::fs::read(path).unwrap();
    assert!(bytes.len() <= 1_048_576, "bounded mathematical packet");
    clean_kernel::with_decode_resource_limits(clean_kernel::DecodeResourceLimits {
        max_nodes: 100_000, max_depth: 128,
    }, || serde_json::from_slice(&bytes)).unwrap()
}

#[test]
fn actual_metadata_word64_value_equation_checked_and_retained() {
    let (bytes, module) = original("case-18-l03_lean_calls_rust");
    let env = tv_anchor_environment().unwrap();
    let claim = goal(&module, 64, false);
    let proof = produce(&module);
    check(&env, &proof, &claim).unwrap();
    audit(&env, &proof, &claim);
    let wrong = goal(&module, 64, true);
    assert!(matches!(check(&env, &proof, &wrong), Err(KernelTypeError::TypeMismatch { .. })));
    let out = output();
    std::fs::create_dir(&out).unwrap();
    std::fs::write(out.join("packet.json"),
                   serde_json::to_vec(&Packet { module_bytes: bytes, proof }).unwrap()).unwrap();
    std::fs::write(out.join("claim.json"), serde_json::to_vec(&claim).unwrap()).unwrap();
}

#[test]
fn fresh_actual_metadata_word64_replay_refuses_real_word32_module() {
    assert_eq!(std::env::var("TRUST_RUST_CALLEE_FORBID_PRODUCER").unwrap(), "1");
    let (bytes, module) = original("case-18-l03_lean_calls_rust");
    let packet = read_packet(&output().join("packet.json"));
    assert_eq!(packet.module_bytes, bytes, "independently expected original module");
    let env = tv_anchor_environment().unwrap();
    let claim = goal(&module, 64, false);
    check(&env, &packet.proof, &claim).unwrap();
    audit(&env, &packet.proof, &claim);
    let (other_bytes, other) = original("case-11-u32");
    assert_ne!(other_bytes, bytes, "a different actual valid metadata module");
    let other_claim = goal(&other, 32, false);
    assert!(matches!(check(&env, &packet.proof, &other_claim),
                     Err(KernelTypeError::TypeMismatch { .. })));
    std::fs::write(output().join("fresh-replay.json"), serde_json::to_vec(&serde_json::json!({
        "producer_forbidden": true, "actual_word32_module_refused": true,
        "scope": "Universal actual-IR value mathematics only; no Rust source TV, ABI, world, NoUB, bytes or admission."
    })).unwrap()).unwrap();
}
