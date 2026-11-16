//! Codec adversaries only. These synthetic data rows are never presented as
//! genuine TCX/source positives or compiler refinement proofs.
use super::*;
use crate::template_key::{self, HoleKey,KeyTy};
fn k(t:KeyTy)->HostKey{template_key::encode(&HoleKey::Type(t)).unwrap()}
fn data()->CapturedSource {
 CapturedSource{bindings:OwnerBindings{owner:(1,2),slots:vec![]},
 target:trust_ir::TargetInfo{triple:"aarch64-apple-darwin".into(),pointer_size:8,
 endianness:trust_ir::Endianness::Little,abi:None,struct_passing:trust_ir::StructPassingPolicy::Unclassified},
 overflow_checks:true,root:0,arena_expressions:3,argument_types:vec![0],argument_variables:vec![Some(11)],modified_variables:vec![],return_type:0,
 types:vec![k(KeyTy::Uint(64)),k(KeyTy::FnDef((3,4),vec![]))],
 nodes:vec![SourceNode{expression:0,ty:0,kind:SourceNodeKind::Call,children:vec![1,2]},
 SourceNode{expression:1,ty:1,kind:SourceNodeKind::Literal,children:vec![]},
 SourceNode{expression:2,ty:0,kind:SourceNodeKind::Variable(11),children:vec![]}],
 effects:vec![SourceEffect::Call{expression:0,key:template_key::encode(&HoleKey::Callee{item:(3,4),args:vec![]}).unwrap(),argument_types:vec![0],result_type:0}]}
}
#[test]
fn source_data_codec_roundtrip_is_not_source_authority(){
 let s=data();let bytes=wire::encode(&s).unwrap();assert_eq!(wire::decode(&bytes,s.bindings()).unwrap(),s);
 for end in 0..bytes.len(){assert!(wire::decode(&bytes[..end],s.bindings()).is_err());}
 let mut extra=bytes.clone();extra.push(0);assert!(wire::decode(&extra,s.bindings()).unwrap_err().0.contains("trailing"));
 let mut schema=bytes;schema[..4].copy_from_slice(&0u32.to_le_bytes());assert!(wire::decode(&schema,s.bindings()).unwrap_err().0.contains("schema"));
}
#[test]
fn source_call_omission_or_extra_effect_refuses(){
 let mut s=data();s.effects.clear();assert!(wire::encode(&s).unwrap_err().0.contains("population"));
 let mut s=data();s.effects.push(s.effects[0].clone());assert!(wire::encode(&s).unwrap_err().0.contains("extra source effect"));
}
#[test]
fn source_graph_cannot_drop_or_reorder_original_children(){
 let mut s=data();s.nodes.pop();assert!(wire::encode(&s).unwrap_err().0.contains("child/root is absent"));
 let mut s=data();s.nodes.swap(1,2);assert!(wire::encode(&s).unwrap_err().0.contains("unrooted/reordered"));
 let mut s=data();s.nodes[0].children[1]=1;assert!(wire::encode(&s).unwrap_err().0.contains("shared/cyclic"));
}
#[test]
fn source_callee_and_argument_types_stay_bound_to_original_children(){
 let mut s=data();let SourceEffect::Call{key,..}=&mut s.effects[0]else{panic!()};*key=template_key::encode(&HoleKey::Callee{item:(8,9),args:vec![]}).unwrap();
 assert!(wire::encode(&s).unwrap_err().0.contains("callee key differs"));
 let mut s=data();let SourceEffect::Call{argument_types,..}=&mut s.effects[0]else{panic!()};argument_types[0]=1;
 assert!(wire::encode(&s).unwrap_err().0.contains("actual argument child"));
}
#[test]
fn source_keys_and_locations_cannot_be_duplicated_or_retyped(){
 let mut s=data();s.types.push(s.types[0].clone());assert!(wire::encode(&s).unwrap_err().0.contains("duplicate source type"));
 let mut s=data();s.nodes[1].expression=2;assert!(wire::encode(&s).unwrap_err().0.contains("duplicate/out-of-arena"));
 let mut s=data();s.nodes[2].ty=2;assert!(wire::encode(&s).unwrap_err().0.contains("type index"));
 let mut s=data();s.nodes[2].ty=1;assert!(wire::encode(&s).unwrap_err().0.contains("parameter variable type"));
}
#[test]
fn source_parameter_and_assignment_facts_cannot_be_detached(){
 let mut s=data();s.argument_variables.clear();assert!(wire::encode(&s).unwrap_err().0.contains("argument/variable"));
 let mut s=data();s.argument_variables.push(Some(11));s.argument_types.push(0);assert!(wire::encode(&s).unwrap_err().0.contains("duplicate source parameter"));
 let mut s=data();s.modified_variables=vec![11,11];assert!(wire::encode(&s).unwrap_err().0.contains("modified-variable"));
}

#[test]
fn source_store_roots_and_exact_values_keep_original_variable_evidence(){
 let mut s=data();s.types=vec![k(KeyTy::Tuple(vec![])),k(KeyTy::RawPtr{mutable:true,pointee:Box::new(KeyTy::Uint(8))}),k(KeyTy::Uint(8))];
 s.root=0;s.arena_expressions=5;s.return_type=0;s.argument_types=vec![1,2];s.argument_variables=vec![Some(10),Some(11)];
 s.nodes=vec![SourceNode{expression:0,ty:0,kind:SourceNodeKind::Block,children:vec![1]},
 SourceNode{expression:1,ty:0,kind:SourceNodeKind::EscapingStore,children:vec![2,4]},
 SourceNode{expression:2,ty:2,kind:SourceNodeKind::Dereference,children:vec![3]},
 SourceNode{expression:3,ty:1,kind:SourceNodeKind::Variable(10),children:vec![]},
 SourceNode{expression:4,ty:2,kind:SourceNodeKind::Variable(11),children:vec![]}];
 s.effects=vec![SourceEffect::Store{expression:1,root:SourceRoot::Argument(0),value_type:2,exact_argument:Some(1)}];
 wire::encode(&s).unwrap();
 for root in [SourceRoot::Argument(1),SourceRoot::Indirect]{
  let mut bad=s.clone();let SourceEffect::Store{root:recorded,..}=&mut bad.effects[0]else{panic!()};*recorded=root;
  assert!(wire::encode(&bad).unwrap_err().0.contains("root/value argument"));
 }
 for exact in [Some(0),None]{
  let mut bad=s.clone();let SourceEffect::Store{exact_argument,..}=&mut bad.effects[0]else{panic!()};*exact_argument=exact;
  assert!(wire::encode(&bad).unwrap_err().0.contains("root/value argument"));
 }
 let mut bad=s;bad.modified_variables.push(10);
 assert!(wire::encode(&bad).unwrap_err().0.contains("root/value argument"));
}

#[test]
fn original_effect_input_cannot_be_ignored_or_replaced_by_thir(){
 use crate::rmeta_entry::{Evidence,EvidenceCall,EvidenceEffectKind};
 let call=EvidenceCall{ids:vec![(3,4)],site:None,equivalence:None,enum_result:false,enum_args:vec![false]};
 let source=concrete::OriginalFacts{argument_enum:vec![false],return_enum:false,calls:vec![call.clone()],stores:vec![],unsupported_call:false};
 let evidence=Evidence{arg_count:1,arg_enum:vec![false],effects:vec![(EvidenceEffectKind::Call(call),0)],..Default::default()};
 binding::original_population(&evidence,&source).unwrap();
 let mut bad=evidence.clone();bad.effects.clear();assert!(binding::original_population(&bad,&source).unwrap_err().0.contains("effect identity/site/value/population"));
 let mut bad=evidence.clone();bad.effects.push((EvidenceEffectKind::Assert(0),1));assert!(binding::original_population(&bad,&source).unwrap_err().0.contains("non-call/store"));
 let mut bad=evidence.clone();let EvidenceEffectKind::Call(call)=&mut bad.effects[0].0 else{panic!()};call.ids=vec![(8,9)];assert!(binding::original_population(&bad,&source).unwrap_err().0.contains("effect identity/site/value/population"));
 let mut bad=evidence.clone();let EvidenceEffectKind::Call(call)=&mut bad.effects[0].0 else{panic!()};call.ids.push((8,9));assert!(binding::original_population(&bad,&source).unwrap_err().0.contains("alias/equivalence"));
 let mut bad=evidence.clone();let EvidenceEffectKind::Call(call)=&mut bad.effects[0].0 else{panic!()};call.site=Some("forged".into());assert!(binding::original_population(&bad,&source).is_err());
 let mut bad=evidence.clone();bad.arg_enum[0]=true;assert!(binding::original_population(&bad,&source).is_err());
 let mut bad=evidence;bad.effects.push(bad.effects[0].clone());assert!(binding::original_population(&bad,&source).unwrap_err().0.contains("effect identity/site/value/population"));
}
