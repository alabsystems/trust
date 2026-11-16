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
struct Observer;
impl rustc_driver::Callbacks for Observer {
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:rustc_middle::ty::TyCtxt<'tcx>)->rustc_driver::Compilation {
  let out=std::path::PathBuf::from(std::env::var_os("CALLABLE_OBSERVER_OUT").unwrap());std::fs::create_dir_all(&out).unwrap();
  let mut rows=vec![];let mut defs:Vec<_>=tcx.hir_body_owners().collect();defs.sort_by_key(|d|tcx.def_path_str(*d));
  for def in defs {let name=rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(def.to_def_id()));
   let Ok((thir,root))=tcx.thir_body(def)else{continue};let thir=thir.borrow();
   let ordinary=producer::lower_module_from_thir_for_query(tcx,def,&thir,root).0;
   let mut row=json!({"name":name,"runtime_unsupported":ordinary.unsupported,"runtime_flags":{"symbolic":ordinary.symbolic,"zst_closure_arg":ordinary.zst_closure_arg,"opaque_collapse":ordinary.opaque_collapse},"runtime_module":ordinary.module,"proof_authority":false});
   match pending::lower_record(tcx,def,&thir,root) {
    Ok(None)=>{row["template"]=json!("not generic");},Err(e)=>{row["template_refusal"]=json!(e.reason());},
    Ok(Some(record))=>match record.capture {Err(e)=>row["capture_refusal"]=json!(format!("{e:?}")),Ok(candidate)=>{
     row["candidate"]=json!(format!("{:?}",candidate.facts));row["sentinel"]=json!(candidate.module);
     if name == "two_instances" {
      assert_eq!(candidate.facts.callee_holes.len(),2);
      assert_ne!(candidate.facts.callee_holes[0].key,candidate.facts.callee_holes[1].key);
      assert_ne!(candidate.facts.callee_holes[0].decl,candidate.facts.callee_holes[1].decl);
      let mut changed=candidate.clone();changed.facts.callee_holes[0].dependencies[0].1=trust_ir::template::TemplateArg::Type(trust_ir::TyG::Ext(trust_ir::TemplateRef::Param(trust_ir::ParamId::new(1))));
      assert!(pending::assemble(&changed,&Names(tcx,def.to_def_id()),name.clone()).is_err());
      changed=candidate.clone();changed.facts.owner=None;
      assert!(pending::assemble(&changed,&Names(tcx,def.to_def_id()),name.clone()).is_err());
      row["distinct_instantiations_and_hostile_binding_controls"]=json!(true);
     }

     match pending::assemble(&candidate,&Names(tcx,def.to_def_id()),name.clone()) {Err(e)=>row["assembly_refusal"]=json!(e.reason()),Ok(pending_template)=>{
       let template=pending_template.template();
       // Exercise the unchanged production builder on the same actual source
       // capture. Empty classes are test input, not conservation authority.
       let production_record=entry::TemplateRecord {body_kind:record.body_kind,capture:Ok(candidate.clone())};
       let inputs=entry::TemplateInputs {record:Some(&production_record),duplicated:false,capture_on:true,clean_origin:false,verdict:entry::VerdictInput::Classes(vec![]),identity:name.clone()};
       let production=entry::template_row(&inputs,&Names(tcx,def.to_def_id()));
       assert!(matches!(production,entry::EntryRefusal::TemplatePending(_) | entry::EntryRefusal::UnnamedCallee(_) | entry::EntryRefusal::Invalid(_) | entry::EntryRefusal::CallerLocation(_)),"unexpected production outcome: {production:?}");
       if name=="tracked" {assert!(matches!(production,entry::EntryRefusal::CallerLocation(_)));}
       row["production_no_admission"]=json!({"class":production.class(),"reason":production.reason(),"entry_bytes":false,"scope":"direct frozen-builder control; no conservation or encoded-metadata authority claimed"});
       let unchecked=entry::TemplateInputs {record:Some(&production_record),duplicated:false,capture_on:true,clean_origin:false,verdict:entry::VerdictInput::Unchecked("not checked by this observer".into()),identity:name.clone()};
       let refusal=entry::template_row(&unchecked,&Names(tcx,def.to_def_id()));
       if name=="tracked" {assert!(matches!(refusal,entry::EntryRefusal::CallerLocation(_)));}
       else {assert!(matches!(refusal,entry::EntryRefusal::ConservationUnchecked(_)));}
      let sv=trust_ir_build::template::validate_template(&template);row["S_violations"]=json!(format!("{sv:?}"));row["template_text"]=json!(format!("{template:?}"));
      let bytes=trust_ir::binary::serialize_template(&template).unwrap();assert_eq!(&trust_ir::binary::deserialize_template(&bytes).unwrap(),template);
      std::fs::write(out.join(format!("{}.trirs",format!("body-{}",def.local_def_index.as_u32()))),bytes).unwrap();
      row["extraction"]=json!(format!("{:?}",pending::check_extraction(&candidate,&pending_template)));
      match trust_ir_build::template::skolem_instance(&template){Err(e)=>row["skolem_error"]=json!(format!("{e:?}")),Ok(m)=>{row["R_violations"]=json!(format!("{:?}",trust_ir_build::validate::validate_module(&m)));row["skolem_module"]=json!(m);}}
     }}
    }}
   }
   std::fs::write(out.join(format!("{}.json",format!("body-{}",def.local_def_index.as_u32()))),serde_json::to_vec_pretty(&row).unwrap()).unwrap();rows.push(row);
  }
  assert_eq!(rows.len(),17);
  for expected in ["apply_mut","apply_once","apply_ref","apply_result","identity","relay","twice","two_instances","unit_output"] {
   let row=rows.iter().find(|r|r["name"]==expected).unwrap();
   assert_eq!(row["S_violations"],"[]");assert_eq!(row["R_violations"],"[]");assert_eq!(row["extraction"],"Ok(())");
   assert_eq!(row["production_no_admission"]["entry_bytes"],false);
  }
  let tracked=rows.iter().find(|r|r["name"]=="tracked").unwrap();assert_eq!(tracked["production_no_admission"]["class"],"caller-location");
  std::fs::write(out.join("ALL.json"),serde_json::to_vec_pretty(&rows).unwrap()).unwrap();
  rustc_driver::Compilation::Stop
 }
}
fn main(){let mut args:Vec<_>=std::env::args().collect();args.extend(["-Zno-steal-thir".into(),"--sysroot".into(),std::env::var("CALLABLE_SYSROOT").unwrap()]);rustc_driver::run_compiler(&args,&mut Observer);}
