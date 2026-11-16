use super::source_record::{self as record, Body, CallKind, Operand, Record};
use clean_kernel::{Environment, Expr, KernelTypeError, Level, TypeChecker};
use clean_reflect::{denote_function, tv_anchor_environment, tv_proof_term, tv_statement};
use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use trust_ir::{CallingConv, Module, Producer, Ty};

#[derive(Serialize, Deserialize)]
struct Packet {
    entry_bytes: Vec<u8>,
    source_bytes: Vec<u8>,
    module_bytes: Vec<u8>,
    proof: Expr,
}

fn captures() -> PathBuf {
    std::env::var_os("TRUST_SOURCE_PAIR_CAPTURES").expect("original paired inputs").into()
}
fn output() -> PathBuf {
    std::env::var_os("TRUST_SOURCE_PAIR_MATH_OUT").expect("fresh owned output").into()
}
fn original() -> (Vec<u8>, Vec<u8>, Vec<u8>, Record, Module) {
    let root = captures();
    let entry = std::fs::read(root.join("core-callee.entry")).unwrap();
    let source = std::fs::read(root.join("core-callee.source")).unwrap();
    let module = std::fs::read(root.join("core-callee.module")).unwrap();
    let claim = record::decode(&source).unwrap();
    assert_eq!(record::encode(&claim).unwrap(), source, "exact canonical original source claim");
    let actual = trust_ir::binary::deserialize_module(&module).unwrap();
    assert_eq!(trust_ir::binary::serialize_module(&actual).unwrap(), module,
               "exact whole original IR module; no normalized/synthesized body");
    assert!(trust_ir_build::validate_module(&actual).is_empty());
    assert_eq!(actual.functions.len(), 1);
    assert!(!actual.functions[0].is_declaration());
    assert_eq!(actual.functions[0].producer, Some(Producer::TRust));
    assert_eq!(actual.functions[0].calling_conv, CallingConv::Rust);
    let report: serde_json::Value = serde_json::from_slice(
        &std::fs::read(root.join("CORE-CALLEE.json")).unwrap()).unwrap();
    assert_eq!(report["owner"].as_str().unwrap(), format!("{:?}", claim.owner));
    assert_eq!(report["source_hash"].as_str().unwrap(), claim.source_hash);
    // The report, source claim and entry remain unlicensed input DATA.
    // No owner/hash agreement constructs a live snapshot or confers source TV.
    (entry, source, module, claim, actual)
}

/// Interpret only the explicitly bounded source-model vocabulary. This reads
/// no output IR, names no arbitrary callee model and constructs no source proof.
fn source_value(source: &Record) -> Result<Expr, &'static str> {
    source.validate().map_err(|_| "malformed source claim")?;
    let arity = source.parameters.len() as u32;
    let operand = |value: &Operand| match value {
        Operand::Parameter(index) => Expr::bvar(arity - index - 1),
        Operand::Literal(value) => Expr::nat_lit_u128(*value as u128),
    };
    match &source.body {
        Body::Operand { value, .. } => Ok(operand(value)),
        Body::Call { kind: CallKind::RegisteredWrappingAdd, generic_u64: true, operands, .. } => {
            Ok(Expr::apps(Expr::const_str("Nat.mod"), [
                Expr::apps(Expr::const_str("Nat.add"),
                           [operand(&operands[0].1), operand(&operands[1].1)]),
                Expr::nat_lit_u128(1u128 << 64),
            ]))
        }
        Body::Call { .. } => Err("ordinary call requires its own independently checked callee semantics"),
    }
}
fn goal(source: &Record, module: &Module) -> Result<Expr, &'static str> {
    let rhs = source_value(source)?;
    let function = &module.functions[0];
    let signature = module.func_type(function.ty).unwrap();
    if signature.params != vec![Ty::U64; source.parameters.len()] || signature.returns != [Ty::U64] {
        return Err("source/IR signature mismatch");
    }
    let actual = denote_function(module, function).map_err(|_| "IR outside reflected value fragment")?;
    if actual.arity as usize != source.parameters.len() || actual.width != 64 || !actual.callees.is_empty() {
        return Err("IR needs separate closed-callee/value semantics");
    }
    Ok(tv_statement(&[], actual.arity, &actual.body, &rhs))
}
fn check(env: &Environment, proof: &Expr, claim: &Expr) -> Result<(), KernelTypeError> {
    assert!(!proof.has_fvar_quick() && !proof.has_loose_bvars());
    let mut checker = TypeChecker::new(env);
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.check_type(claim, &Expr::sort(Level::zero())).unwrap();
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
    assert!(std::env::var_os("TRUST_SOURCE_PAIR_FORBID_PRODUCER").is_none(),
            "fresh reader must not produce a replacement proof");
    let actual = denote_function(module, &module.functions[0]).unwrap();
    tv_proof_term(&[], actual.arity, &actual.body)
}
fn negative_sources(original: &Record) -> (Record, Record, Record) {
    let mut duplicate = original.clone();
    let Body::Call { operands, .. } = &mut duplicate.body else { panic!("actual original intrinsic") };
    operands[1].1 = Operand::Parameter(0);
    let mut constant = original.clone();
    constant.body = Body::Operand { node: 0, value: Operand::Literal(7) };
    let mut ordinary = original.clone();
    let Body::Call { kind, .. } = &mut ordinary.body else { unreachable!() };
    *kind = CallKind::OrdinaryCall;
    // Each is a valid data record. None can recreate a live TCX snapshot.
    for record in [&duplicate, &constant, &ordinary] { record::encode(record).unwrap(); }
    (duplicate, constant, ordinary)
}
#[test]
fn actual_source_model_and_original_ir_value_equation_retained() {
    let (entry_bytes, source_bytes, module_bytes, source, module) = original();
    assert!(matches!(source.body, Body::Call { kind: CallKind::RegisteredWrappingAdd, .. }));
    let env = tv_anchor_environment().unwrap();
    let claim = goal(&source, &module).unwrap();
    let proof = produce(&module);
    check(&env, &proof, &claim).unwrap();
    audit(&env, &proof, &claim);
    let (duplicate, constant, ordinary) = negative_sources(&source);
    for wrong in [&duplicate, &constant] {
        assert!(matches!(check(&env, &proof, &goal(wrong, &module).unwrap()),
                         Err(KernelTypeError::TypeMismatch { .. })));
    }
    assert!(goal(&ordinary, &module).is_err(), "ordinary call must not acquire primitive semantics");
    let out = output();
    std::fs::create_dir(&out).unwrap();
    std::fs::write(out.join("packet.json"), serde_json::to_vec(&Packet {
        entry_bytes, source_bytes, module_bytes, proof,
    }).unwrap()).unwrap();
    std::fs::write(out.join("claim.json"), serde_json::to_vec(&claim).unwrap()).unwrap();
}
#[test]
fn fresh_source_model_replay_reconstructs_claim_and_rejects_false_models() {
    assert_eq!(std::env::var("TRUST_SOURCE_PAIR_FORBID_PRODUCER").unwrap(), "1");
    let (entry, source_bytes, module_bytes, source, module) = original();
    let bytes = std::fs::read(output().join("packet.json")).unwrap();
    assert!(bytes.len() <= 1_048_576);
    let packet: Packet = clean_kernel::with_decode_resource_limits(
        clean_kernel::DecodeResourceLimits { max_nodes: 100_000, max_depth: 128 },
        || serde_json::from_slice(&bytes)).unwrap();
    assert_eq!(packet.entry_bytes, entry);
    assert_eq!(packet.source_bytes, source_bytes);
    assert_eq!(packet.module_bytes, module_bytes);
    let env = tv_anchor_environment().unwrap();
    let claim = goal(&source, &module).unwrap();
    check(&env, &packet.proof, &claim).unwrap();
    audit(&env, &packet.proof, &claim);
    let (duplicate, constant, ordinary) = negative_sources(&source);
    for wrong in [&duplicate, &constant] {
        assert!(matches!(check(&env, &packet.proof, &goal(wrong, &module).unwrap()),
                         Err(KernelTypeError::TypeMismatch { .. })));
    }
    assert!(goal(&ordinary, &module).is_err());
    std::fs::write(output().join("fresh-replay.json"), serde_json::to_vec(&serde_json::json!({
        "producer_forbidden": true, "duplicate_source_operand_kernel_refused": true,
        "constant_source_value_kernel_refused": true, "ordinary_call_model_refused": true,
        "scope": "Unlicensed source-model/IR returned-value mathematics only; no source authenticity, Rust-source TV, world/ABI/NoUB or admission."
    })).unwrap()).unwrap();
}
