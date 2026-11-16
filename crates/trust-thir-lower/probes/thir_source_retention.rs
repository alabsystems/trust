//! Genuine actual-owner THIR source capture observation; no IR/source proof.
#![feature(rustc_private)]
extern crate rustc_target;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_abi;
extern crate trust_ir;
extern crate trust_ir_build;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
extern crate serde_json;
extern crate trust_thir_lower;
use rustc_middle::ty::{self,TyCtxt};
use rustc_middle::thir::ExprKind;
use rustc_span::def_id::LocalDefId;
use trust_thir_lower::effect_conservation::thir_source::{capture,concrete,SourceEffect,SourceRoot};
fn named(tcx:TyCtxt<'_>,name:&str)->LocalDefId{
 let found:Vec<_>=tcx.hir_crate_items(()).definitions().filter(|&d|tcx.opt_item_name(d.to_def_id()).is_some_and(|n|n.as_str()==name)).collect();
 assert_eq!(found.len(),1,"actual source {name}");found[0]
}
use trust_thir_lower::{template_metadata::{self as meta,instantiate::{self,TemplateProvider}},template_lowering::pending,rmeta_entry::{self as entry,EntryNames,CalleeNameRefusal}};
use std::collections::HashMap;
struct Names<'tcx>(TyCtxt<'tcx>,rustc_span::def_id::DefId);
impl EntryNames for Names<'_>{
 fn body_symbol(&self)->Result<String,String>{Err("template has no runtime symbol".into())}
 fn body_abi(&self)->trust_thir_lower::calling_convention::FunctionAbi{trust_thir_lower::calling_convention::FunctionAbi::RUST}
 fn body_requires_caller_location(&self)->bool{false}
 fn callee_symbol(&self,_:usize,_:&trust_thir_lower::CalleeRef)->Result<String,CalleeNameRefusal>{Err(CalleeNameRefusal::Unnamed("only actual typed generic holes in fixture".into()))}
 fn static_symbol(&self,_:rustc_span::def_id::DefId)->Result<String,String>{Err("no fixture static".into())}
 fn file_name(&self,p:&str)->Result<String,String>{Ok(p.into())}
 fn target_info(&self)->trust_ir::TargetInfo{let t=&self.0.sess.target;trust_ir::TargetInfo{triple:t.llvm_target.to_string(),pointer_size:u32::from(t.pointer_width/8),endianness:match t.endian{rustc_abi::Endian::Little=>trust_ir::Endianness::Little,rustc_abi::Endian::Big=>trust_ir::Endianness::Big},abi:None,struct_passing:trust_ir::StructPassingPolicy::Unclassified}}
}
struct ActualSourceProvider{bytes:HashMap<rustc_span::def_id::DefId,Vec<u8>>}
impl<'tcx> TemplateProvider<'tcx> for ActualSourceProvider{
 fn load(&mut self,tcx:TyCtxt<'tcx>,owner:rustc_span::def_id::DefId)->Result<meta::AuthenticatedTemplate,meta::MetadataError>{
  meta::read(self.bytes.get(&owner).expect("actual source fixture dependency"),&meta::rustc::owner_bindings(tcx,owner)?,tcx.sess.overflow_checks())
 }
}
fn actual_template<'tcx>(tcx:TyCtxt<'tcx>,name:&str)->(rustc_span::def_id::DefId,trust_ir::template::Template,trust_thir_lower::effect_conservation::thir_source::CapturedSource,Vec<u8>){
 let owner=named(tcx,name);let (stored,root)=tcx.thir_body(owner).unwrap();let thir=stored.borrow();
 let record=pending::lower_record(tcx,owner,&thir,root).unwrap().unwrap();let candidate=record.capture.unwrap();
 let assembled=pending::assemble(&candidate,&Names(tcx,owner.to_def_id()),name.into()).unwrap();
 let source=capture::local(tcx,owner).unwrap();let bindings=meta::rustc::owner_bindings(tcx,owner.to_def_id()).unwrap();
 // Diagnostic framing inputs only: these counts/ledger are not a canonical
 // D28 producer verdict. Real original THIR and actual pending source lowering
 // supply the independent source/candidate images used by this analysis probe.
 let ledger=assembled.template().header.holes.iter().filter_map(|h|{
  if let trust_ir::template::HoleKind::Callee{decl}=h.kind{
   let trust_thir_lower::template_key::HoleKey::Callee{item,..}=trust_thir_lower::template_key::decode(&h.key).unwrap()else{panic!()};
   Some(entry::EvidenceLedgerRow{func_id:decl.index(),ids:vec![item],site:None})
  }else{None}
 }).collect();
 let effects=source.effects().iter().map(|e|match e{
  SourceEffect::Call{expression,key,argument_types,..}=>{
   let trust_thir_lower::template_key::HoleKey::Callee{item,..}=trust_thir_lower::template_key::decode(key).unwrap()else{panic!()};
   (entry::EvidenceEffectKind::Call(entry::EvidenceCall{ids:vec![item],site:None,equivalence:None,enum_result:false,enum_args:vec![false;argument_types.len()]}),*expression)
  }
  _=>panic!("this diagnostic pending-source framing fixture has no store effects"),
 }).collect();
 let evidence=entry::encode_evidence(&entry::Evidence{effects,arg_count:source.argument_types().len()as u32,arg_enum:vec![false;source.argument_types().len()],ledger,..Default::default()});
 assert_eq!(source.bindings(),&bindings);
 (owner.to_def_id(),assembled.template().clone(),source,evidence)
}
// Change an authenticated input only after its first actual provider read.
// A custody cache must still reconstruct and re-read the complete graph.
struct ChangingProvider {
 bytes:HashMap<rustc_span::def_id::DefId,Vec<u8>>,
 owner:rustc_span::def_id::DefId, alternate:Vec<u8>, reads:usize,
}
impl<'tcx> TemplateProvider<'tcx> for ChangingProvider {
 fn load(&mut self,tcx:TyCtxt<'tcx>,owner:rustc_span::def_id::DefId)->Result<meta::AuthenticatedTemplate,meta::MetadataError>{
  let bytes=if owner==self.owner {self.reads+=1;if self.reads>1 {&self.alternate}else{&self.bytes[&owner]}}else{&self.bytes[&owner]};
  meta::read(bytes,&meta::rustc::owner_bindings(tcx,owner)?,tcx.sess.overflow_checks())
 }
}
struct Probe;
impl rustc_driver::Callbacks for Probe{
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->rustc_driver::Compilation{
  let mut rows=Vec::new();
  for (name,calls,stores) in [("leaf",0,0),("root",1,0),("source_store",0,1),("source_alias_store",0,1),("source_reassigned_pointer",0,1),("source_reassigned_value",0,1),("source_private",0,0),("source_array",0,0),("source_pending_drop",0,0),("source_ground",1,0)]{
   let owner=named(tcx,name);let source=capture::local(tcx,owner).unwrap();
   assert_eq!(source.bindings(),&trust_thir_lower::template_metadata::rustc::owner_bindings(tcx,owner.to_def_id()).unwrap());
   assert!(source.visited_expressions()>0 && !source.type_keys().is_empty());
   assert_eq!(source.effects().iter().filter(|e|matches!(e,SourceEffect::Call{..})).count(),calls);
   assert_eq!(source.effects().iter().filter(|e|matches!(e,SourceEffect::Store{..})).count(),stores);
   if name=="root"{
    assert_eq!(source.bindings().slots.len(),3,"original lifetime/type/const positions");
    let SourceEffect::Call{key,..}=&source.effects()[0]else{panic!()};
    let term=trust_thir_lower::template_key::decode(key).unwrap();
    let trust_thir_lower::template_key::HoleKey::Callee{item,args}=term else{panic!()};
    assert_eq!(item,trust_thir_lower::template_key::rustc::stable_def(tcx,named(tcx,"leaf").to_def_id()));
    assert!(matches!(&args[1],trust_thir_lower::template_key::KeyArg::Type(trust_thir_lower::template_key::KeyTy::Param(1))));
    assert!(matches!(&args[2],trust_thir_lower::template_key::KeyArg::Const(trust_thir_lower::template_key::KeyConst::Param(2))));
   }
   if stores==1{
    let SourceEffect::Store{root,exact_argument,..}=&source.effects()[0]else{panic!()};
    if name=="source_store"{assert_eq!(root,&SourceRoot::Argument(0));assert_eq!(*exact_argument,Some(1));}
    if name=="source_alias_store"{assert_eq!(root,&SourceRoot::Indirect);assert_eq!(*exact_argument,Some(1));}
    if name=="source_reassigned_pointer"{assert_eq!(root,&SourceRoot::Indirect);assert_eq!(*exact_argument,Some(2));}
    if name=="source_reassigned_value"{assert_eq!(root,&SourceRoot::Argument(0));assert_eq!(*exact_argument,None);}
   }
   rows.push(serde_json::json!({"case":name,"actual_owner":true,"source_nodes":source.visited_expressions(),"original_type_keys":source.type_keys().len(),"calls":calls,"stores":stores,"capture_only":true,"concrete_drop_check_required":true,"source_refinement_or_admission":false}));
  }
  let mut refusals=Vec::new();
  for name in ["source_bad_borrow","source_bad_index","source_bad_branch","source_bad_arithmetic","source_bad_closure"]{
   let reason=match capture::local(tcx,named(tcx,name)){Err(e)=>e.0,Ok(_)=>panic!("incomplete source scope accepted: {name}")};
   assert!(reason.starts_with("THIR source facts:"));refusals.push(serde_json::json!({"case":name,"reason":reason}));
  }
  let mut concrete_rows=Vec::new();let mut concrete_refusals=Vec::new();
  let main=named(tcx,"main");let (stored,_)=tcx.thir_body(main).unwrap();let main_thir=stored.borrow();
  for (_,expr) in main_thir.exprs.iter_enumerated(){
   let ExprKind::Call{fun,..}=&expr.kind else{continue};
   let ty::FnDef(def,args)=*main_thir[*fun].ty.kind()else{continue};
   let name=tcx.item_name(def).to_string();
   if !["root","source_ground","source_store","source_alias_store","source_reassigned_pointer","source_reassigned_value","source_array","source_pending_drop"].contains(&name.as_str()){continue}
   let resolved=ty::Instance::try_resolve(tcx,ty::TypingEnv::fully_monomorphized(),def,args.skip_binder()).unwrap().unwrap();
   let source=capture::local(tcx,def.expect_local()).unwrap();
   let concrete=match concrete::instantiate(tcx,resolved,&source){
    Ok(c)=>{assert_ne!(name,"source_pending_drop");c},
    Err(e)=>{assert_eq!(name,"source_pending_drop");assert!(e.0.contains("complete drop/scope"));concrete_refusals.push(serde_json::json!({"case":name,"reason":e.0,"actual_instance_from_source_call":true}));continue}
   };
   assert_eq!(concrete.instance(),resolved);
   if name=="root"{let concrete::ConcreteEffect::Call(call)=&concrete.effects()[0]else{panic!()};assert_eq!(call.resolved().def_id(),named(tcx,"leaf").to_def_id());assert_ne!(call.resolved_key(),call.original_key());}
   if name=="source_ground"{let concrete::ConcreteEffect::Call(call)=&concrete.effects()[0]else{panic!()};assert!(call.original_call().unwrap().site.is_some());}
   if name=="source_store" && matches!(resolved.args.type_at(0).kind(),ty::Adt(..)){
    assert_eq!(concrete.argument_enum(),&[false,true]);
    assert_eq!(concrete.original_argument_enum(),&[false,false]);
    assert_eq!(concrete.original_store_facts(),&[(0,2,None)]);assert!(!concrete.enum_types().is_empty());
    let concrete::ConcreteEffect::Store{value_class,exact_argument,..}=&concrete.effects()[0]else{panic!()};assert_eq!(*value_class,0);assert_eq!(*exact_argument,Some(1));
   }
   let wrong=capture::local(tcx,named(tcx,"source_private")).unwrap();
   let reason=match concrete::instantiate(tcx,resolved,&wrong){Err(e)=>e.0,Ok(_)=>panic!("wrong original source owner accepted")};assert!(reason.contains("owner/full positional"));
   concrete_refusals.push(serde_json::json!({"case":"wrong_original_owner","for":name,"reason":reason}));
   concrete_rows.push(serde_json::json!({"case":name,"actual_instance_from_source_call":true,"enum_arguments":concrete.argument_enum(),"enum_type_population":concrete.enum_types().len(),"source_refinement_or_admission":false}));
  }
  assert_eq!(concrete_rows.len(),10);assert_eq!(concrete_refusals.len(),11);
  let mut provider=ActualSourceProvider{bytes:HashMap::new()};let mut templates=HashMap::new();
  for name in ["leaf","root","source_chain","source_diamond","source_identity","source_const_array","source_typed_relay","source_value_chain"]{
   let (owner,t,source,evidence)=actual_template(tcx,name);
   let bytes=meta::frame_with_source(source.bindings(),&t,tcx.sess.overflow_checks(),&evidence,&source).unwrap();
   let read=meta::read(&bytes,source.bindings(),tcx.sess.overflow_checks()).unwrap();
   let Some(meta::SourceRetention::Captured(retained))=read.source()else{panic!()};assert_eq!(retained,&source);
   if let Some(directory)=std::env::var_os("SOURCE_FACTS_OUT"){
    let directory=std::path::PathBuf::from(directory);std::fs::create_dir_all(&directory).unwrap();let id=source.bindings().owner;
    std::fs::write(directory.join(format!("{:016x}-{:016x}.s2",id.0,id.1)),&bytes).unwrap();
   }
   provider.bytes.insert(owner,bytes);templates.insert(owner,(t,source,evidence));
  }
  let mut graphs=Vec::new();let mut graph_refusals=Vec::new();let mut diamond_instance=None;
  for (_,expr) in main_thir.exprs.iter_enumerated(){
   let ExprKind::Call{fun,..}=&expr.kind else{continue};let ty::FnDef(def,args)=*main_thir[*fun].ty.kind()else{continue};
   let name=tcx.item_name(def).to_string();if !["root","source_chain","source_diamond","source_identity","source_const_array","source_typed_relay","source_value_chain"].contains(&name.as_str()){continue}
   let instance=ty::Instance::try_resolve(tcx,ty::TypingEnv::fully_monomorphized(),def,args.skip_binder()).unwrap().unwrap();
   let result=instantiate::construct_source_checked_with(tcx,instance,&mut provider);
   if name=="source_diamond"{diamond_instance=Some(instance);}
   let graph=result.unwrap();
   let records=graph.source_checks().unwrap();
   let expected=match name.as_str(){"root"|"source_typed_relay"|"source_value_chain"=>2,"source_chain"=>3,"source_diamond"=>4,_=>1};assert_eq!(records.len(),expected);
   assert_eq!(graph.callables().len(),records.len());
   for callable in graph.callables(){
    let actual=tcx.fn_abi_of_instance(ty::TypingEnv::fully_monomorphized().as_query_input((callable.instance(),ty::List::empty()))).unwrap();
    assert!(std::ptr::eq(actual,callable.fn_abi()));callable.validate(graph.module()).unwrap();
    let key=trust_thir_lower::template_key::rustc::checked_call_key(tcx,callable.instance().def_id(),callable.instance().args,callable.instance().def_id()).unwrap();
    let key=trust_thir_lower::template_key::encode(&key).unwrap();
    assert!(records.iter().any(|s|s.body()==callable.function()&&s.instance_key()==&key));
   }
   if name=="source_typed_relay"{
    let f=&graph.module().functions[0];let sig=graph.module().func_type(f.ty).unwrap();
    if instance.args.types().any(|t|t.is_unit()) {assert_eq!(sig.params[1],trust_ir::Ty::Unit);assert!(sig.returns.is_empty());}
    else {let trust_ir::Ty::Array(element,3)=sig.params[1]else{panic!("actual shifted array parameter")};assert!(element.index()>0,"nonzero parent type namespace");}
   }
   for callable in graph.callables(){let ret=callable.fn_abi().ret.layout.ty;let f=graph.module().function_by_id(callable.function()).unwrap();if ret.is_array()&&!ret.is_unit(){assert_eq!(graph.module().func_type(f.ty).unwrap().returns.len(),1,"array ZST is not Unit-return erasure");}}
   if instance.args.types().any(|t|t.is_unit()) {
    for callable in graph.callables(){assert!(callable.fn_abi().ret.layout.ty.is_unit());assert!(matches!(callable.fn_abi().ret.mode,rustc_target::callconv::PassMode::Ignore));let f=graph.module().function_by_id(callable.function()).unwrap();assert!(graph.module().func_type(f.ty).unwrap().returns.is_empty());}
    if name=="source_value_chain" {
     let body=&graph.module().functions[0];let calls:Vec<_>=body.instructions().filter_map(|n|if let trust_ir::Inst::Call{args,..}=&n.inst{assert!(n.results.is_empty());Some(args)}else{None}).collect();assert_eq!(calls.len(),2);
     let units:Vec<_>=body.instructions().filter(|n|matches!(n.inst,trust_ir::Inst::Const{ty:trust_ir::Ty::Unit,value:trust_ir::Constant::PhantomData})).flat_map(|n|n.results.iter().copied()).collect();
     assert!(calls[1].iter().any(|v|units.contains(v)),"later call consumes the retained original Unit SSA value");
     let before=graph.module().stable_digest();assert_eq!(instantiate::construct_source_checked_with(tcx,instance,&mut provider).unwrap().module().stable_digest(),before,"deterministic actual Unit graph");
    }
   }
   assert!(graph.module().functions.iter().all(|f|f.body_gate==Some(trust_ir::BodyGate::Ungated)));
   assert!(graph.module().proof_obligations.is_empty()&&graph.module().proof_certificates.is_empty());
   graphs.push(serde_json::json!({"case":name,"source_bound_records":records.len(),"actual_fnabi_records":graph.callables().len(),"actual_args":format!("{args:?}"),"actual_source_lowering":true,"canonical_metadata_writer_or_compiler":false,"source_refinement_or_admission":false}));
   // Remove one actual source call from the real pending IR while preserving
   // a structurally typed (but poisonous) replacement. This hostile image
   // must not satisfy the unchanged retained source call population.
   let good=provider.bytes[&def].clone();let (mut altered,source,evidence)=templates[&def].clone();
   if !source.effects().iter().any(|e|matches!(e,SourceEffect::Call{..})){
    for mutation in ["argument","return","legacy"]{
     let mut original=entry::decode_evidence(&evidence).unwrap();
     if mutation=="argument"{original.arg_enum[0]=true}else if mutation=="return"{original.ret_enum=true}
     let bytes=if mutation=="legacy"{meta::frame(source.bindings(),&altered,tcx.sess.overflow_checks(),&evidence).unwrap()}
       else{meta::frame_with_source(source.bindings(),&altered,tcx.sess.overflow_checks(),&entry::encode_evidence(&original),&source).unwrap()};
     provider.bytes.insert(def,bytes);
     let reason=match instantiate::construct_source_checked_with(tcx,instance,&mut provider){Err(e)=>e.0,Ok(_)=>panic!("original no-call fact ignored: {mutation}")};
     assert!(reason.contains("original"),"{reason}");graph_refusals.push(serde_json::json!({"case":format!("no_call_original_{mutation}"),"reason":reason}));
    }
    provider.bytes.insert(def,good);continue
   }
   let call_returns:HashMap<_,_>=altered.module.functions.iter().filter_map(|f|{
    let returns=&altered.module.func_types[f.ty.as_usize()].returns;
    (returns.len()==1).then(||(f.id,returns[0].clone()))
   }).collect();
   let mut changed=false;
   for block in &mut altered.module.functions[0].blocks {for node in &mut block.body{
    if let trust_ir::InstG::Call{callee,..}=node.inst{if !changed{
     node.inst=trust_ir::InstG::Undef{ty:call_returns[&callee].clone()};changed=true;
    }}
   }}assert!(changed);
   let bad=meta::frame_with_source(source.bindings(),&altered,tcx.sess.overflow_checks(),&evidence,&source).unwrap();provider.bytes.insert(def,bad);
   let reason=match instantiate::construct_source_checked_with(tcx,instance,&mut provider){Err(e)=>e.0,Ok(_)=>panic!("source call omission accepted")};
   if instance.args.types().any(|t|t.is_unit()){assert!(reason.contains("Unit return adapter")&&reason.contains("undefined"),"{reason}");}else{assert!(reason.contains("source consistency"),"{reason}");}graph_refusals.push(serde_json::json!({"case":"actual_source_call_omitted","for":name,"reason":reason}));
   let mut omitted=entry::decode_evidence(&evidence).unwrap();assert!(!omitted.effects.is_empty());omitted.effects.pop();
   let omitted=entry::encode_evidence(&omitted);
   let bytes=meta::frame_with_source(source.bindings(),&templates[&def].0,tcx.sess.overflow_checks(),&omitted,&source).unwrap();provider.bytes.insert(def,bytes);
   let reason=match instantiate::construct_source_checked_with(tcx,instance,&mut provider){Err(e)=>e.0,Ok(_)=>panic!("original census deletion ignored")};
   assert!(reason.contains("original effect identity/site/value/population"));graph_refusals.push(serde_json::json!({"case":"original_census_call_omitted","reason":reason}));
   for mutation in ["site","identity","argument","return","call_enum","audited_equivalence"]{
    let mut changed=entry::decode_evidence(&evidence).unwrap();
    match mutation{
     "argument"=>changed.arg_enum[0]=true,"return"=>changed.ret_enum=true,
     _=>{let entry::EvidenceEffectKind::Call(call)=&mut changed.effects[0].0 else{panic!()};match mutation{
      "site"=>call.site=Some("forged-original-site".into()),"identity"=>call.ids[0]=(0,0),"call_enum"=>call.enum_args[0]=true,
      "audited_equivalence"=>call.equivalence=Some(7),_=>unreachable!(),
     }}
    }
    let bytes=meta::frame_with_source(source.bindings(),&templates[&def].0,tcx.sess.overflow_checks(),&entry::encode_evidence(&changed),&source).unwrap();provider.bytes.insert(def,bytes);
    let reason=match instantiate::construct_source_checked_with(tcx,instance,&mut provider){Err(e)=>e.0,Ok(_)=>panic!("contradictory original fact ignored: {mutation}")};
    assert!(reason.contains("original"),"{reason}");graph_refusals.push(serde_json::json!({"case":format!("original_fact_{mutation}"),"reason":reason}));
   }
   // S1 remains unlicensed data, and cannot be used as a source-bound child.
   let legacy=meta::frame(source.bindings(),&templates[&def].0,tcx.sess.overflow_checks(),&evidence).unwrap();provider.bytes.insert(def,legacy);
   let reason=match instantiate::construct_source_checked_with(tcx,instance,&mut provider){Err(e)=>e.0,Ok(_)=>panic!("legacy source absence accepted")};assert!(reason.contains("lacks retained original"));graph_refusals.push(serde_json::json!({"case":"legacy_source_absence","reason":reason}));
   provider.bytes.insert(def,good);
  }
  // The root itself and a transitive leaf must both be re-read before
  // reusing any earlier checked image. Both alternate envelopes are valid;
  // only their retained input bytes/debug path differ, without a source claim.
  let instance=diamond_instance.unwrap();
  for name in ["root","leaf"] {
   let owner=named(tcx,name).to_def_id();let (mut changed,source,evidence)=templates[&owner].clone();
   assert!(!changed.module.files.is_empty(),"actual source file table");
   changed.module.files[0].push_str(".changed-input");
   let alternate=meta::frame_with_source(source.bindings(),&changed,tcx.sess.overflow_checks(),&evidence,&source).unwrap();
   meta::read(&alternate,&meta::rustc::owner_bindings(tcx,owner).unwrap(),tcx.sess.overflow_checks()).unwrap();
   let mut changing=ChangingProvider{bytes:provider.bytes.clone(),owner,alternate,reads:0};
   let reason=match instantiate::construct_source_checked_with(tcx,instance,&mut changing){
    Err(e)=>e.0,Ok(_)=>panic!("changed {name} input bypassed complete reconstruction"),
   };
   assert!(changing.reads>=2 && reason.contains("checked input changed"),"{name}: {reason}");
   graph_refusals.push(serde_json::json!({"case":format!("rechecked_{name}_input_changed"),"provider_reads":changing.reads,"reason":reason}));
  }
  assert_eq!(graphs.len(),15);assert_eq!(graph_refusals.len(),89);
  println!("{}",serde_json::to_string_pretty(&serde_json::json!({"source_captures":rows,"source_scope_refusals":refusals,"concrete_rows":concrete_rows,"concrete_refusals":concrete_refusals,"constructed_source_graphs":graphs,"constructed_source_refusals":graph_refusals,"canonical_new_compiler":false,"new_capture_reads_MIR_body":false})).unwrap());
  rustc_driver::Compilation::Continue
 }
}
fn main(){let mut args:Vec<_>=std::env::args().collect();args.push("-Zno-steal-thir".into());rustc_driver::run_compiler(&args,&mut Probe);}
