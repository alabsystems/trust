#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_hir;
extern crate rustc_span;
extern crate rustc_abi;
extern crate trust_thir_lower as producer;
extern crate trust_ir;
extern crate trust_ir_build;
extern crate serde_json;
use producer::rmeta_entry::{self as entry, EntryNames, CalleeNameRefusal};
use producer::template_lowering::pending;
use serde_json::json;
struct Names<'tcx>(rustc_middle::ty::TyCtxt<'tcx>, rustc_span::def_id::DefId);
impl EntryNames for Names<'_> {
 fn body_symbol(&self)->Result<String,String>{Err("template body has no runtime symbol".into())}
 fn body_abi(&self)->trust_thir_lower::calling_convention::FunctionAbi{trust_thir_lower::calling_convention::FunctionAbi::RUST}
 fn body_requires_caller_location(&self)->bool{self.0.codegen_fn_attrs(self.1).flags.contains(rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags::TRACK_CALLER)}
 fn callee_symbol(&self,_:usize,_:&producer::CalleeRef)->Result<String,CalleeNameRefusal>{Err(CalleeNameRefusal::Unnamed("every generic callee requires its actual owner-bound hole".into()))}
 fn static_symbol(&self,_:rustc_span::def_id::DefId)->Result<String,String>{Err("fixture has no statics".into())}
 fn file_name(&self,p:&str)->Result<String,String>{Ok(p.into())}
 fn target_info(&self)->trust_ir::TargetInfo{let t=&self.0.sess.target;trust_ir::TargetInfo{triple:t.llvm_target.to_string(),pointer_size:u32::from(t.pointer_width/8),endianness:match t.endian{rustc_abi::Endian::Little=>trust_ir::Endianness::Little,rustc_abi::Endian::Big=>trust_ir::Endianness::Big},abi:None,struct_passing:trust_ir::StructPassingPolicy::Unclassified}}
}
// The captured source body and owner are real. Empty effect evidence is
// deliberately non-authoritative; the constructor and every result stay Ungated.
struct Captured(std::collections::HashMap<rustc_span::def_id::DefId,Vec<u8>>);
impl<'tcx> producer::template_metadata::instantiate::TemplateProvider<'tcx> for Captured {
 fn load(&mut self,tcx:rustc_middle::ty::TyCtxt<'tcx>,owner:rustc_span::def_id::DefId)->Result<producer::template_metadata::AuthenticatedTemplate,producer::template_metadata::MetadataError>{
  producer::template_metadata::read(self.0.get(&owner).expect("actual captured owner"),&producer::template_metadata::rustc::owner_bindings(tcx,owner)?,tcx.sess.overflow_checks())
 }
}
struct Observer;
impl rustc_driver::Callbacks for Observer {
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:rustc_middle::ty::TyCtxt<'tcx>)->rustc_driver::Compilation {
  let mut provider=Captured(Default::default());
  for def in tcx.hir_body_owners() {
   let name=tcx.opt_item_name(def.to_def_id()).map(|n|n.to_string()).unwrap_or_default();
   if !["identity","relay"].contains(&name.as_str()){continue;}
   let (body,root)=tcx.thir_body(def).unwrap();let body=body.borrow();
   let record=pending::lower_record(tcx,def,&body,root).unwrap().unwrap();
   let candidate=record.capture.expect("real generic source capture");
   producer::template_metadata::rustc::check_capture(tcx,def.to_def_id(),&candidate.facts).unwrap();
   let assembled=pending::assemble(&candidate,&Names(tcx,def.to_def_id()),name.clone()).unwrap();
   let t=assembled.template();assert!(trust_ir_build::template::validate_template(t).is_empty());
   let argc=candidate.module.func_types[candidate.module.functions[0].ty.as_usize()].params.len() as u32;
   let ledger=candidate.callees.iter().map(|c|{
    let mut ids=vec![];
    for def in [c.site_def_id,c.def_id] {
     let hash=tcx.def_path_hash(def);let stable=(hash.stable_crate_id().as_u64(),hash.local_hash().as_u64());
     if !ids.contains(&stable){ids.push(stable);}
    }
    assert!(c.site_args.is_none(),"fixture's generic hole uses a complete checked key rather than a concrete site spelling");
    entry::EvidenceLedgerRow{func_id:c.func_id.index(),ids,site:None}
   }).collect();
   let facts=entry::encode_evidence(&entry::Evidence{arg_count:argc,arg_enum:vec![false;argc as usize],ledger,..Default::default()});
   let bindings=producer::template_metadata::rustc::owner_bindings(tcx,def.to_def_id()).unwrap();
   provider.0.insert(def.to_def_id(),producer::template_metadata::frame(&bindings,t,tcx.sess.overflow_checks(),&facts).unwrap());
   let retained=entry::TemplateRecord{body_kind:record.body_kind,capture:Ok(candidate)};
   let inputs=entry::TemplateInputs{record:Some(&retained),duplicated:false,capture_on:true,clean_origin:false,verdict:entry::VerdictInput::Unchecked("observer has no source-refinement authority".into()),identity:name};
   assert!(matches!(entry::template_row(&inputs,&Names(tcx,def.to_def_id())),entry::EntryRefusal::ConservationUnchecked(_)));
  }
  let main=tcx.hir_body_owners().find(|d|tcx.opt_item_name(d.to_def_id()).is_some_and(|n|n.as_str()=="main")).unwrap();
  let (body,_)=tcx.thir_body(main).unwrap();let body=body.borrow();let mut rows=vec![];
  for expr in &body.exprs {
   let rustc_middle::thir::ExprKind::Call{fun,..}=expr.kind else{continue};
   let rustc_middle::ty::FnDef(owner,args)=*body.exprs[fun].ty.kind() else{continue};
   if !provider.0.contains_key(&owner){continue;}
   let args=tcx.erase_and_anonymize_regions(args.skip_binder());
   let instance=rustc_middle::ty::Instance::try_resolve(tcx,rustc_middle::ty::TypingEnv::fully_monomorphized(),owner,args).unwrap().unwrap();
   let name=tcx.item_name(owner).to_string();let description=format!("{name}{args:?}");
   match producer::template_metadata::instantiate::construct_with(tcx,instance,&mut provider) {
    Err(e)=>panic!("actual callable construction {description} failed: {e}"),
    Ok(result)=>{
     assert!(trust_ir_build::validate::validate_module(result.module()).is_empty());
     assert!(result.module().functions.iter().all(|f|!f.is_declaration()&&f.body_gate==Some(trust_ir::BodyGate::Ungated)));
     assert_eq!(result.callables().len(),result.module().functions.len());
     for binding in result.callables(){
      binding.validate(result.module()).unwrap();
      let actual=tcx.fn_abi_of_instance(rustc_middle::ty::TypingEnv::fully_monomorphized().as_query_input((binding.instance(),rustc_middle::ty::List::empty()))).unwrap();
      assert!(std::ptr::eq(binding.fn_abi(),actual),"retained the actual query object");
      assert_eq!(result.module().function_by_id(binding.function()).unwrap().name,tcx.symbol_name(binding.instance()).name);
      let mut wrong=result.module().clone();wrong.function_by_id_mut(binding.function()).unwrap().name.push_str("_different");assert!(binding.validate(&wrong).is_err());
      wrong=result.module().clone();wrong.function_by_id_mut(binding.function()).unwrap().attrs.readonly=true;assert!(binding.validate(&wrong).is_err());
      wrong=result.module().clone();wrong.function_by_id_mut(binding.function()).unwrap().calling_conv=trust_ir::CallingConv::C;assert!(binding.validate(&wrong).is_err());
     }
     if name=="relay" {
      assert_eq!(result.callables().len(),2);
      let root=&result.module().functions[0];let sig=result.module().func_type(root.ty).unwrap();
      let trust_ir::Ty::Array(element,3)=sig.params[1] else{panic!("actual array parameter")};
      assert!(element.index()>0,"fixture must exercise nonzero host type IDs");
     }
     rows.push(json!({"instance":description,"constructed_bodies":result.callables().len(),"actual_fn_abi_custody":true,"canonical_namespace":true,"header_mutations_refused":3*result.callables().len(),"ungated":true,"proof_authority":false,"graph_digest":format!("{:?}",result.graph_digest())}));
    }
   }
  }
  assert_eq!(rows.len(),7);assert_eq!(rows.iter().filter(|r|r["actual_fn_abi_custody"]==true).count(),7);
  println!("{}",serde_json::to_string_pretty(&json!({"status":"PASS_HEADER_AND_FNABI_CUSTODY_ONLY","source_refinement":false,"canonical_new_compiler":false,"rows":rows})).unwrap());
  rustc_driver::Compilation::Stop
 }
}
fn main(){let mut args:Vec<_>=std::env::args().collect();args.push("-Zno-steal-thir".into());rustc_driver::run_compiler(&args,&mut Observer);}
