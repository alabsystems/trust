//! Installation-core data controls only. These private test images never call
//! bind_upstream, fabricate a TyCtxt, or claim a canonical R admission token.

use std::collections::BTreeMap;

use trust_ir::{Block, BlockId, CallingConv, Ty, ValueId};

use super::super::append_instance_body;
use super::*;

fn image(name: &str, body: bool, callee: Option<&str>) -> Module {
    let mut module = Module::new("installation_data");
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    let mut function = Function::new(FuncId::new(0), name, signature, BlockId::new(0));
    // link_symbol::declaration_producer leaves ordinary nonlocal rows unknown.
    function.producer = body.then_some(Producer::TRust);
    function.calling_conv = CallingConv::Rust;
    if body {
        let mut block = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::U64);
        let result = if callee.is_some() {
            block.body.push(
                trust_ir::InstrNode::new(trust_ir::Inst::Call {
                    callee: FuncId::new(1),
                    args: vec![ValueId::new(0)],
                })
                .with_result(ValueId::new(1)),
            );
            ValueId::new(1)
        } else {
            ValueId::new(0)
        };
        block.body.push(trust_ir::InstrNode::new(trust_ir::Inst::Return { values: vec![result] }));
        function.blocks.push(block);
    }
    module.try_add_function(function).unwrap();
    if let Some(callee) = callee {
        let mut declaration = Function::new(FuncId::new(1), callee, signature, BlockId::new(0));
        declaration.producer = None;
        declaration.calling_conv = CallingConv::Rust;
        module.try_add_function(declaration).unwrap();
    }
    module
}

fn data_binding(base: &Arc<Module>, slot: FuncId, guest: &Module) -> BoundDeclaration {
    // Private raw test data for the mutation core, not the actual-TCX constructor.
    let original = base.function_by_id(slot).unwrap().clone();
    BoundDeclaration {
        base: Arc::clone(base),
        signature: base.func_type(original.ty).unwrap().clone(),
        original,
        guest: guest.clone(),
    }
}

#[test]
fn r_assembly_transport_identity_requires_definition_and_entire_instance_key() {
    assert!(producer_facts_compatible(None, Some(&Producer::TRust)));
    assert!(producer_facts_compatible(Some(&Producer::TRust), Some(&Producer::TRust)));
    assert!(!producer_facts_compatible(Some(&Producer::Clean), Some(&Producer::TRust)));
    assert!(!producer_facts_compatible(None, None));
    assert!(!producer_facts_compatible(None, Some(&Producer::Clean)));
    assert!(check_identity_facts(Some("d"), Some("k1"), "d", "k1").is_ok());
    for (definition, concrete) in [
        (None, Some("k1")),
        (Some("d"), None),
        (Some("other"), Some("k1")),
        (Some("d"), Some("k2")),
    ] {
        assert!(check_identity_facts(definition, concrete, "d", "k1").is_err());
    }
}

#[test]
fn r_assembly_transport_plain_modern_symbol_collision_still_refuses() {
    let mut host = image("_RLeaf", false, None);
    let before = host.clone();
    let guest = image("_RLeaf", true, None);
    let error =
        append_instance_body(None, &mut host, &guest, 0, true, &BTreeMap::new()).unwrap_err();
    assert!(error.contains("already holds"), "{error}");
    assert_eq!(host, before);
    assert!(
        trust_thir_lower::instance_admission::declaration_name_matches(
            "_RLeaf", "up::leaf", "d", "k"
        )
        .is_err()
    );
}

#[test]
fn r_assembly_transport_data_install_preserves_id_and_rejects_stale_guest_or_host() {
    let base = Arc::new(image("_RLeaf", false, None));
    let guest = image("_RLeaf", true, None);
    let binding = data_binding(&base, FuncId::new(0), &guest);
    let mut host = (*base).clone();
    let id =
        append_instance_body(Some(&binding), &mut host, &guest, 0, true, &BTreeMap::new()).unwrap();
    assert_eq!(id, FuncId::new(0));
    assert_eq!(host.functions.len(), 1);
    assert!(!host.functions[0].is_declaration());
    assert_eq!(base.functions[0], binding.original);
    assert!(base.functions[0].is_declaration());
    for mutation in 0..4 {
        let mut host = (*base).clone();
        let mut supplied = guest.clone();
        match mutation {
            0 => supplied.functions[0].blocks[0].params[0].1 = Ty::I64,
            1 => host.functions[0].name.push_str("_other"),
            2 => host.func_types[0].params[0] = Ty::I64,
            _ => {
                let mut duplicate = host.functions[0].clone();
                duplicate.id = FuncId::new(1);
                host.functions.push(duplicate);
            }
        }
        let before = host.clone();
        assert!(
            append_instance_body(Some(&binding), &mut host, &supplied, 0, true, &BTreeMap::new())
                .is_err()
        );
        assert_eq!(host, before, "mutation {mutation} must be transactional");
    }
}

#[test]
fn r_assembly_transport_data_nested_install_retains_original_and_incoming_edge_ids() {
    let mut original = image("_RRoot", false, None);
    let mut leaf_decl = original.functions[0].clone();
    leaf_decl.id = FuncId::new(1);
    leaf_decl.name = "_RLeaf".into();
    original.functions.push(leaf_decl);
    let base = Arc::new(original);
    let mut host = (*base).clone();
    let leaf = image("_RLeaf", true, None);
    let leaf_binding = data_binding(&base, FuncId::new(1), &leaf);
    let leaf_id =
        append_instance_body(Some(&leaf_binding), &mut host, &leaf, 0, true, &BTreeMap::new())
            .unwrap();
    let middle = image("_RMiddle", true, Some("_RLeaf"));
    let middle_id = append_instance_body(
        None,
        &mut host,
        &middle,
        1,
        true,
        &BTreeMap::from([(FuncId::new(1), leaf_id)]),
    )
    .unwrap();
    let root = image("_RRoot", true, Some("_RMiddle"));
    let root_binding = data_binding(&base, FuncId::new(0), &root);
    let root_id = append_instance_body(
        Some(&root_binding),
        &mut host,
        &root,
        1,
        true,
        &BTreeMap::from([(FuncId::new(1), middle_id)]),
    )
    .unwrap();
    assert_eq!((root_id, leaf_id, middle_id), (FuncId::new(0), FuncId::new(1), FuncId::new(2)));
    assert!(
        matches!(&host.functions[0].blocks[0].body[0].inst, trust_ir::Inst::Call { callee, .. } if *callee == middle_id)
    );
    assert!(
        matches!(&host.functions[2].blocks[0].body[0].inst, trust_ir::Inst::Call { callee, .. } if *callee == leaf_id)
    );
    assert!(base.functions.iter().all(Function::is_declaration));
    let before = host.clone();
    assert!(append_instance_body(None, &mut host, &leaf, 0, true, &BTreeMap::new()).is_err());
    assert_eq!(host, before, "only the existing actual-Instance slot cache reuses a body");
}

#[test]
fn r_assembly_transport_replacement_synthesizes_pending_claims_and_refuses_exhaustion() {
    let base = Arc::new(image("_RLeaf", false, None));
    let mut guest = image("_RLeaf", true, None);
    guest.functions[0].proofs.push(trust_ir::proof::ProofAnnotation::NoPanic);
    let binding = data_binding(&base, FuncId::new(0), &guest);
    let mut host = (*base).clone();
    append_instance_body(Some(&binding), &mut host, &guest, 0, true, &BTreeMap::new()).unwrap();
    assert_eq!(host.proof_obligations.len(), 1);
    assert_eq!(host.proof_obligations[0].function, Some(FuncId::new(0)));
    assert_eq!(host.proof_obligations[0].status, trust_ir::proof::ProofStatus::Pending);
    let mut host = (*base).clone();
    host.proof_obligations.push(trust_ir::proof::ProofObligation::new(
        trust_ir::value::ProofId::new(u32::MAX),
        trust_ir::proof::ObligationKind::PanicFreedom,
        trust_ir::proof::ProofStatus::Pending,
        "exhausted unrelated obligation id",
    ));
    let before = host.clone();
    let error = append_instance_body(Some(&binding), &mut host, &guest, 0, true, &BTreeMap::new())
        .unwrap_err();
    assert!(error.contains("exhausted"), "{error}");
    assert_eq!(host, before);
}

#[test]
fn r_assembly_transport_existing_relink_keeps_the_installed_body_edge_without_a_name_exception() {
    let mut original = image("_REntry", true, Some("_RLeaf"));
    original.functions[1].producer = Some(Producer::TRust);
    let base = Arc::new(original);
    let leaf = image("_RLeaf", true, None);
    let binding = data_binding(&base, FuncId::new(1), &leaf);
    let mut host = (*base).clone();
    let leaf_id =
        append_instance_body(Some(&binding), &mut host, &leaf, 0, true, &BTreeMap::new()).unwrap();
    let entry = image("_REntry", true, Some("_RLeaf"));
    let before = host.clone();
    super::super::relink_monomorphic_body(
        &mut host,
        FuncId::new(0),
        &entry,
        1,
        true,
        &BTreeMap::from([(FuncId::new(1), leaf_id)]),
        &|_, _| Err("a modern name is not the legacy declaration exception".into()),
    )
    .unwrap();
    assert_eq!(host, before, "the already authenticated same-ID body edge stays unchanged");
}
