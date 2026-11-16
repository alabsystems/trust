//! Minimal synthetic checker observation only: no TCX, Rust source or admission proof.
//! Extra IR effects are deliberately not reported by the source matcher. Preserve
//! the raw outcome as an open source-census integrity/model limitation.
#![feature(rustc_private)]
extern crate rustc_driver;
extern crate serde_json;
extern crate trust_ir;
extern crate trust_thir_lower;
use trust_ir::{Block,BlockId,FuncId,FuncTy,Function,Inst,InstrNode,Module,Producer,Ty,ValueId};
use trust_thir_lower::{effect_conservation::retained::judge,rmeta_entry::{Evidence,EvidenceCall,EvidenceEffectKind,EvidenceLedgerRow}};
fn main() {
    let mut module=Module::new("synthetic_census_asymmetry");
    module.target_info=Some(trust_ir::TargetInfo{triple:"arm64-apple-macosx".into(),pointer_size:8,
        endianness:trust_ir::Endianness::Little,abi:None,struct_passing:trust_ir::StructPassingPolicy::Unclassified});
    let ty=module.add_func_type(FuncTy::unrecorded(vec![Ty::U64],vec![Ty::U64],false)).unwrap();
    let mut block=Block::new(BlockId::new(0)).with_param(ValueId::new(0),Ty::U64);
    block.body.push(InstrNode::new(Inst::Call{callee:FuncId::new(1),args:vec![ValueId::new(0)]}).with_result(ValueId::new(1)));
    block.body.push(InstrNode::new(Inst::Return{values:vec![ValueId::new(1)]}));
    let mut root=Function::new(FuncId::new(0),"synthetic_root",ty,BlockId::new(0)).with_producer(Producer::TRust);
    root.blocks.push(block);module.try_add_function(root).unwrap();
    module.try_add_function(Function::new(FuncId::new(1),"synthetic_declaration",ty,BlockId::new(0))).unwrap();
    let mut evidence=Evidence{arg_count:1,arg_enum:vec![false],
        effects:vec![(EvidenceEffectKind::Call(EvidenceCall{ids:vec![(11,22)],site:None,equivalence:None,enum_result:false,enum_args:vec![false]}),0)],
        ledger:vec![EvidenceLedgerRow{func_id:1,ids:vec![(11,22)],site:None}],..Evidence::default()};
    let before=judge(&module,&evidence).unwrap();
    assert!(before.tags().is_empty(),"structural control must be well-formed");
    evidence.effects.clear();
    let after=judge(&module,&evidence);
    let (accepted,detail)=match after {Ok(result)=>(result.tags().is_empty(),format!("{:?}",result.tags())),Err(error)=>(false,error.to_string())};
    println!("{}",serde_json::json!({"scope":"SYNTHETIC_CHECKER_OBSERVATION_NO_TCX_NO_ADMISSION_NO_PROOF_AUTHORITY", "baseline_tags":format!("{:?}",before.tags()),"source_call_census_removed":true,"module_call_and_ledger_unchanged":true,"accepted_by_retained_checker":accepted,"detail":detail,"source":"crates/trust-thir-lower/src/effect_conservation.rs::unpaired_effects","limitation_open":accepted}));
}
