use trust_ir::{
    Block, BlockId, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Module, Producer, Ty,
    ValueId,
};

use super::judge;
use crate::effect_conservation::{Lane, TagKind};
use crate::rmeta_entry::{self, Evidence, EvidenceEffectKind};

fn store() -> (Module, Evidence) {
    let mut module = Module::new("retained_store_population");
    let signature = module.add_func_type(FuncTy::unrecorded(vec![Ty::Ptr], vec![], false)).unwrap();
    let mut block = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::Ptr);
    block.body.push(
        InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(false) })
            .with_result(ValueId::new(1)),
    );
    block.body.push(InstrNode::new(Inst::Store {
        ty: Ty::Bool,
        ptr: ValueId::new(0),
        value: ValueId::new(1),
        volatile: false,
        align: None,
    }));
    block.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    let mut body = Function::new(FuncId::new(0), "body", signature, BlockId::new(0))
        .with_producer(Producer::TRust);
    body.blocks.push(block);
    module.try_add_function(body).unwrap();
    let evidence = Evidence {
        arg_count: 1,
        arg_enum: vec![false],
        effects: vec![(EvidenceEffectKind::Store(0), 0)],
        store_values: vec![(0, 0)],
        ..Evidence::default()
    };
    (module, evidence)
}

fn wire(evidence: &Evidence) -> Evidence {
    rmeta_entry::decode_evidence(&rmeta_entry::encode_evidence(evidence)).unwrap()
}

#[test]
fn retained_coarse_store_keeps_its_enum_value_abstraction() {
    let (module, evidence) = store();
    let result = judge(&module, &wire(&evidence)).unwrap();
    assert_eq!(
        result.tags().iter().map(|t| t.kind).collect::<Vec<_>>(),
        vec![TagKind::Abstracted(Lane::OpaqueLane)],
    );
}

#[test]
fn retained_coarse_store_values_cannot_be_removed_or_rebound() {
    let (module, evidence) = store();
    let mut missing = evidence.clone();
    missing.store_values.clear();
    let mut rebound = evidence;
    rebound.store_values[0].0 = u32::MAX;
    for malformed in [missing, rebound] {
        let error = match judge(&module, &wire(&malformed)) {
            Ok(_) => panic!("malformed coarse store facts erased the enum-value abstraction"),
            Err(error) => error,
        };
        assert!(error.0.contains("complete store-effect order"), "{error}");
    }
}

#[test]
fn retained_drop_filter_preserves_original_exact_store_ordinals() {
    let (module, mut evidence) = store();
    evidence.effects = vec![
        (EvidenceEffectKind::Drop { destructor: false }, 0),
        (EvidenceEffectKind::Store(u32::MAX), 1),
    ];
    evidence.store_values[0].0 = u32::MAX;
    evidence.exact_store_args = vec![(1, 0)];
    evidence.drop_oracle = Some(vec![]);
    let result = judge(&module, &wire(&evidence)).unwrap();
    assert_eq!(
        result.tags().iter().map(|t| t.kind).collect::<Vec<_>>(),
        vec![TagKind::Abstracted(Lane::OpaqueLane)],
    );
}
