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
use serde_json::json;
use producer::rmeta_entry::{self as entry, EntryNames, CalleeNameRefusal};
use producer::template_lowering::pending;
struct Names<'tcx>(rustc_middle::ty::TyCtxt<'tcx>,rustc_span::def_id::DefId);
impl EntryNames for Names<'_> {
 fn body_symbol(&self)->Result<String,String>{Err("a template has no runtime body symbol".into())}
 fn body_abi(&self)->trust_thir_lower::calling_convention::FunctionAbi{trust_thir_lower::calling_convention::FunctionAbi::RUST}
 fn body_requires_caller_location(&self)->bool{self.0.codegen_fn_attrs(self.1).flags.contains(rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags::TRACK_CALLER)}
 fn callee_symbol(&self,_:usize,_:&producer::CalleeRef)->Result<String,CalleeNameRefusal>{Err(CalleeNameRefusal::Unnamed("source fixture requires every generic callable to have an authentic hole".into()))}
 fn static_symbol(&self,_:rustc_span::def_id::DefId)->Result<String,String>{Err("no fixture static".into())}
 fn file_name(&self,p:&str)->Result<String,String>{Ok(p.into())}
 fn target_info(&self)->trust_ir::TargetInfo{let t=&self.0.sess.target;trust_ir::TargetInfo{triple:t.llvm_target.to_string(),pointer_size:u32::from(t.pointer_width/8),endianness:match t.endian{rustc_abi::Endian::Little=>trust_ir::Endianness::Little,rustc_abi::Endian::Big=>trust_ir::Endianness::Big},abi:None,struct_passing:trust_ir::StructPassingPolicy::Unclassified}}
}
// This provider authenticates actual captured data, but its empty evidence is
// deliberately NOT a source-conservation judgement. Construction stays Ungated.
struct CapturedData(std::collections::HashMap<rustc_span::def_id::DefId, Vec<u8>>);
impl<'tcx> producer::template_metadata::instantiate::TemplateProvider<'tcx> for CapturedData {
 fn load(&mut self, tcx: rustc_middle::ty::TyCtxt<'tcx>, owner: rustc_span::def_id::DefId) -> Result<producer::template_metadata::AuthenticatedTemplate, producer::template_metadata::MetadataError> {
  let bytes=self.0.get(&owner).expect("actual captured owner");
  producer::template_metadata::read(bytes,&producer::template_metadata::rustc::owner_bindings(tcx,owner)?,tcx.sess.overflow_checks())
 }
}
struct Observer;
impl rustc_driver::Callbacks for Observer {
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:rustc_middle::ty::TyCtxt<'tcx>)->rustc_driver::Compilation {
  use producer::template_key::{HoleKey, KeyTy, KeyConst};
  use trust_ir::template::{HoleKind, TypeContract};
  let mut captured=CapturedData(Default::default());
  let mut rows=vec![];let mut defs:Vec<_>=tcx.hir_body_owners().collect();defs.sort_by_key(|d|tcx.def_path_str(*d));
  for def in defs {
   let name=tcx.opt_item_name(def.to_def_id()).map(|n|n.to_string()).unwrap_or_default();
   if !["identity","bytes","with_lifetime","relay","relay_twice","inspect","nominal","fixed"].contains(&name.as_str()) { continue; }
   let (thir,root)=tcx.thir_body(def).unwrap();let thir=thir.borrow();
   let ordinary=producer::lower_module_from_thir_for_query(tcx,def,&thir,root).0;
   let mut row=json!({"name":name,"runtime_symbolic":ordinary.symbolic,"runtime_unsupported":ordinary.unsupported,"runtime_type_hole":format!("{:?}",ordinary.module).contains("hole_"),"proof_authority":false});
   match pending::lower_record(tcx,def,&thir,root).unwrap() {
    None=>row["capture"]=json!("not generic"),
    Some(record)=>match record.capture {
     Err(e)=>row["capture_refusal"]=json!(format!("{e:?}")),
     Ok(candidate)=>{
      row["facts"]=json!(format!("{:?}",candidate.facts));
      producer::template_metadata::rustc::check_capture(tcx,def.to_def_id(),&candidate.facts).unwrap();
      assert!(!candidate.facts.type_holes.is_empty() || name=="nominal");
      for h in &candidate.facts.type_holes {
       assert!(matches!(h.key,HoleKey::Type(KeyTy::Array(_,KeyConst::Param(_)))));
       assert!(!h.dependencies.is_empty());
       let HoleKey::Type(key)=&h.key else {unreachable!()};
       let actual=producer::template_key::rustc::ty_of_key(tcx,key,def.to_def_id()).unwrap();
       assert_eq!(producer::template_key::rustc::checked_type_key(tcx,actual,def.to_def_id()).unwrap(),*key);
      }
      match pending::assemble(&candidate,&Names(tcx,def.to_def_id()),name.clone()) {
       Err(e)=>row["assembly_refusal"]=json!(e.reason()),
       Ok(p)=>{
        let t=p.template();assert!(trust_ir_build::template::validate_template(t).is_empty());
        assert!(t.header.holes.iter().any(|h|matches!(h.kind,HoleKind::Type{contract:TypeContract::Opaque})));
        assert!(t.header.holes.iter().filter(|h|matches!(h.kind,HoleKind::Type{..})).count()==1);
        assert!(pending::check_extraction(&candidate,&p).is_ok());
        let bytes=trust_ir::binary::serialize_template(t).unwrap();assert_eq!(trust_ir::binary::deserialize_template(&bytes).unwrap(),*t);
        let bindings=producer::template_metadata::rustc::owner_bindings(tcx,def.to_def_id()).unwrap();
        let arg_count=candidate.module.func_types[candidate.module.functions[0].ty.as_usize()].params.len() as u32;
        let non_authoritative=entry::encode_evidence(&entry::Evidence{arg_count,arg_enum:vec![false;arg_count as usize],..Default::default()});
        if candidate.facts.callee_holes.is_empty() { captured.0.insert(def.to_def_id(),producer::template_metadata::frame(&bindings,t,tcx.sess.overflow_checks(),&non_authoritative).unwrap()); }
        row["template"]=json!(format!("{t:?}"));row["canonical_source_type_hole"]=json!(true);
        row["type_holes"]=json!(candidate.facts.type_holes.len());row["callee_holes"]=json!(candidate.facts.callee_holes.len());
        let mut hostile=candidate.clone();hostile.facts.type_holes[0].dependencies.clear();
        assert!(pending::assemble(&hostile,&Names(tcx,def.to_def_id()),name.clone()).is_err());
        hostile=candidate.clone();hostile.facts.type_holes[0].id=trust_ir::HoleId::new(99);
        assert!(pending::assemble(&hostile,&Names(tcx,def.to_def_id()),name.clone()).is_err());
        hostile=candidate.clone();hostile.facts.owner=None;
        assert!(pending::assemble(&hostile,&Names(tcx,def.to_def_id()),name.clone()).is_err());
        row["hostile_owner_argument_and_id_controls"]=json!(true);
        if name=="with_lifetime" {assert_eq!(candidate.facts.parameter_indices,vec![1,2]);}
        if name.starts_with("relay") {
          assert_eq!(candidate.facts.callee_holes.len(),1);
          assert_ne!(candidate.facts.type_holes[0].id,candidate.facts.callee_holes[0].id);
          assert!(matches!(t.header.holes[candidate.facts.callee_holes[0].id.as_usize()].kind,HoleKind::Callee{decl} if decl==candidate.facts.callee_holes[0].decl));
        }
        let production_record=entry::TemplateRecord{body_kind:record.body_kind,capture:Ok(candidate.clone())};
        let inputs=entry::TemplateInputs{record:Some(&production_record),duplicated:false,capture_on:true,clean_origin:false,verdict:entry::VerdictInput::Unchecked("actual source observer is not conservation authority".into()),identity:name.clone()};
        let refusal=entry::template_row(&inputs,&Names(tcx,def.to_def_id()));
        assert!(matches!(refusal,entry::EntryRefusal::ConservationUnchecked(_)));
        row["production_refusal"]=json!(refusal.class());row["entry_bytes"]=json!(false);
       }
      }
     }
    }
   }
   assert_eq!(row["runtime_type_hole"],false);
   rows.push(row);
  }
  for name in ["identity","bytes","with_lifetime","relay","relay_twice"] {
   let row=rows.iter().find(|r|r["name"]==name).unwrap();assert_eq!(row["canonical_source_type_hole"],true,"{row:#}");
  }
  for name in ["inspect","nominal"] {
   let row=rows.iter().find(|r|r["name"]==name).unwrap();assert!(row.get("capture_refusal").is_some()||row.get("assembly_refusal").is_some(),"{row:#}");
  }
  assert_eq!(rows.iter().find(|r|r["name"]=="fixed").unwrap()["capture"],"not generic");
  let main=tcx.hir_body_owners().find(|d|tcx.opt_item_name(d.to_def_id()).is_some_and(|n|n.as_str()=="main")).unwrap();
  let (thir,_)=tcx.thir_body(main).unwrap();let thir=thir.borrow();
  let mut constructions=vec![];
  for expr in &thir.exprs {
   if let rustc_middle::thir::ExprKind::Call{fun,..}=expr.kind {
    if let rustc_middle::ty::FnDef(owner,args)=*thir.exprs[fun].ty.kind() {
     if !captured.0.contains_key(&owner) {continue;}
     let args=tcx.erase_and_anonymize_regions(args.skip_binder());
     let instance=rustc_middle::ty::Instance::try_resolve(tcx,rustc_middle::ty::TypingEnv::fully_monomorphized(),owner,args).unwrap().unwrap();
     let name=tcx.item_name(owner).to_string();
     let artifact=producer::template_metadata::read(captured.0.get(&owner).unwrap(),&producer::template_metadata::rustc::owner_bindings(tcx,owner).unwrap(),tcx.sess.overflow_checks()).unwrap();
     for hole in &artifact.template().header.holes {
      if !matches!(hole.kind,HoleKind::Type{..}) {continue;}
      let image=producer::concrete_type_transport::from_key(tcx,instance,&hole.key).unwrap();
      assert_eq!(image.roots().len(),1);assert!(matches!(image.roots()[0],trust_ir::Ty::Array(_, _)));
      let source_key=producer::template_key::decode(&hole.key).unwrap();let HoleKey::Type(key)=source_key else{unreachable!()};
      let original=producer::template_key::rustc::ty_of_key(tcx,&key,owner).unwrap();
      let direct=producer::concrete_type_transport::lower(tcx,instance,&[original]).unwrap();
      assert_eq!(image.roots(),direct.roots());assert_eq!(image.module().stable_digest(),direct.module().stable_digest());
     }
     let made=producer::template_metadata::instantiate::construct_with(tcx,instance,&mut captured).expect("actual array source/header construction");
     assert!(trust_ir_build::validate::validate_module(made.module()).is_empty());
     assert_eq!(made.callables().len(),made.module().functions.len());
     assert!(made.module().functions.iter().all(|f|!f.is_declaration()&&f.body_gate==Some(trust_ir::BodyGate::Ungated)));
     for binding in made.callables(){
      binding.validate(made.module()).unwrap();
      let actual=tcx.fn_abi_of_instance(rustc_middle::ty::TypingEnv::fully_monomorphized().as_query_input((binding.instance(),rustc_middle::ty::List::empty()))).unwrap();
      assert!(std::ptr::eq(binding.fn_abi(),actual));
     }
     constructions.push(json!({"owner":name,"actual_args":format!("{args:?}"),"actual_captured_key_concrete_image_matches":true,"complete_array_header_construction":true,"actual_fn_abi_custody":true,"ungated":true,"proof_authority":false}));
    }
   }
  }
  assert_eq!(constructions.len(),4);assert!(constructions.iter().all(|r|r["actual_captured_key_concrete_image_matches"]==true));
  rows.push(json!({"constructions":constructions,"source_evidence":"deliberately non-authoritative fixture bytes","proof_authority":false,"runtime_type_hole":false}));
  println!("{}",serde_json::to_string_pretty(&rows).unwrap());
  rustc_driver::Compilation::Stop
 }
}
fn main(){let mut args:Vec<_>=std::env::args().collect();args.push("-Zno-steal-thir".into());rustc_driver::run_compiler(&args,&mut Observer);}
