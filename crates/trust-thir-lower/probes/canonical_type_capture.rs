#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_data_structures;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_hir;
extern crate rustc_span;
extern crate rustc_abi;
extern crate trust_thir_lower as producer;
extern crate sdk_trust_thir_lower;
extern crate trust_ir;
extern crate trust_ir_build;
extern crate serde_json;
use serde_json::json;
use producer::rmeta_entry::{self as entry, EntryNames, CalleeNameRefusal};
use producer::template_lowering::pending;
fn tuple_case(name: &str) -> bool {
 matches!(name,"tuple_identity"|"tuple_nested"|"tuple_forward"|"tuple_two_types"|"tuple_lifetime")
}
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
  let mut tuple_sources=std::collections::HashMap::new();
  let mut rows=vec![];let mut defs:Vec<_>=tcx.hir_body_owners().collect();defs.sort_by_key(|d|tcx.def_path_str(*d));
  for def in defs {
   let name=tcx.opt_item_name(def.to_def_id()).map(|n|n.to_string()).unwrap_or_default();
   if !["identity","bytes","with_lifetime","relay","relay_twice","inspect","nominal","nominal_enum","nominal_array","two_nominals","nominal_field","nominal_construct","nominal_union","ground_nominal","fixed"].contains(&name.as_str()) && !tuple_case(&name) { continue; }
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
      if tuple_case(&name) {
       // Tuples are already structural TyG nodes, unlike nominal ground rows.
       // Do not invent an alternate whole-tuple-hole representation.
       let rustc_middle::thir::BodyTy::Fn(signature)=thir.body_type else{panic!("actual tuple owner signature")};
       let original=signature.inputs().iter().copied().find(|t|matches!(t.kind(),rustc_middle::ty::Tuple(_))).unwrap();
       let key=producer::template_key::rustc::checked_type_key(tcx,original,def.to_def_id()).unwrap();
       assert!(matches!(key,KeyTy::Tuple(_)));
       assert_eq!(producer::template_key::rustc::ty_of_key(tcx,&key,def.to_def_id()).unwrap(),original);
       tuple_sources.insert(def.to_def_id(),original);
       assert!(!candidate.facts.type_holes.iter().any(|h|matches!(h.key,HoleKey::Type(KeyTy::Tuple(_)))));
       let mut wrong=candidate.facts.clone();wrong.owner=None;
       assert!(producer::template_metadata::rustc::check_capture(tcx,def.to_def_id(),&wrong).is_err());
       wrong=candidate.facts.clone();wrong.parameter_indices[0]=u32::MAX;
       assert!(producer::template_metadata::rustc::check_capture(tcx,def.to_def_id(),&wrong).is_err());
       wrong=candidate.facts.clone();wrong.params[0]=producer::template_lowering::LaneParam::Const(trust_ir::Ty::Usize);
       assert!(producer::template_metadata::rustc::check_capture(tcx,def.to_def_id(),&wrong).is_err());
       row["actual_owner_argument_and_type_controls"]=json!(true);
      }
      for h in &candidate.facts.type_holes {
       assert!(matches!(h.key,HoleKey::Type(KeyTy::Array(_,KeyConst::Param(_))|KeyTy::Adt(..))));
       assert!(!h.dependencies.is_empty());
       let HoleKey::Type(key)=&h.key else {unreachable!()};
       let actual=producer::template_key::rustc::ty_of_key(tcx,key,def.to_def_id()).unwrap();
       assert_eq!(producer::template_key::rustc::checked_type_key(tcx,actual,def.to_def_id()).unwrap(),*key);
      }
      match pending::assemble(&candidate,&Names(tcx,def.to_def_id()),name.clone()) {
       Err(e)=>row["assembly_refusal"]=json!(e.reason()),
       Ok(p)=>{
        let t=p.template();assert!(trust_ir_build::template::validate_template(t).is_empty());
        if name=="ground_nominal" {
          // This type is GROUND: T belongs to the function but occurs nowhere
          // in its actual signature/body. Preserve the existing SDK path; it
          // must not acquire a new opaque Type hole or a fabricated refusal.
          let baseline=sdk_trust_thir_lower::template_lowering::pending::lower_record(tcx,def,&thir,root).unwrap().unwrap();
          let baseline=baseline.capture.expect("original SDK ground capture must remain supported");
          assert_eq!(candidate.facts.owner,baseline.facts.owner);
          assert_eq!(candidate.module.stable_digest(),baseline.module.stable_digest());
          use rustc_middle::ty::TypeVisitableExt;
          let original_signature=tcx.fn_sig(def.to_def_id()).instantiate_identity().skip_binder();
          assert!(original_signature.inputs().iter().all(|ty|!ty.has_param()));
          assert!(!original_signature.output().has_param());
          assert_eq!(original_signature.inputs()[0],original_signature.output());
          assert_eq!(candidate.facts.parameter_indices,vec![0]);
          assert_eq!(baseline.facts.parameter_indices,vec![0]);
          assert!(matches!(candidate.facts.params.as_slice(),[producer::template_lowering::LaneParam::Type]));
          assert!(matches!(baseline.facts.params.as_slice(),[sdk_trust_thir_lower::template_lowering::LaneParam::Type]));
          assert!(candidate.facts.type_holes.is_empty()&&baseline.facts.type_holes.is_empty());
          assert!(candidate.facts.callee_holes.is_empty()&&baseline.facts.callee_holes.is_empty());
          assert_eq!(t.header.identity,"ground_nominal");
          assert!(matches!(t.header.params.as_slice(),[trust_ir::template::TemplateParam::Type]));
          assert!(t.header.holes.is_empty());
          assert!(pending::check_extraction(&candidate,&p).is_ok());
          row["unchanged_ground_template_control"]=json!(true);
          row["baseline_same_owner_and_module"]=json!(true);
          row["unused_original_type_parameter"]=json!(true);
          row["header_identity"]=json!(t.header.identity);
          row["type_holes"]=json!(0);row["header_type_holes"]=json!(0);
          row["canonical_source_type_hole"]=json!(false);
        } else {
        if !tuple_case(&name) {
         assert!(t.header.holes.iter().any(|h|matches!(h.kind,HoleKind::Type{contract:TypeContract::Opaque})), "actual owner={} name={} facts={:?} header={:?}",tcx.def_path_str(def),name,candidate.facts,t.header);
         assert!(!candidate.facts.type_holes.is_empty());
         // NOM-CONTROL1: preserve every old array/nominal cardinality exactly.
         assert_eq!(candidate.facts.type_holes.len(), if name=="two_nominals" {2}else{1});
        } else {
         let signature=&t.module.func_types[t.module.functions[0].ty.as_usize()];
         assert!(signature.params.iter().any(|t|matches!(t,trust_ir::TyG::Tuple(_))));
         assert!(matches!(signature.returns.as_slice(),[trust_ir::TyG::Tuple(_)]));
         if name=="tuple_nested" {
          // Only its [u8;N] field is a dependent whole-array Type hole.
          assert_eq!(candidate.facts.type_holes.len(),1);
          assert!(matches!(candidate.facts.type_holes[0].key,HoleKey::Type(KeyTy::Array(_,KeyConst::Param(_)))));
         } else {
          assert_eq!(candidate.facts.type_holes.len(),0);
         }
         row["canonical_structural_tuple"]=json!(true);
        }
        assert_eq!(t.header.holes.iter().filter(|h|matches!(h.kind,HoleKind::Type{..})).count(),candidate.facts.type_holes.len());
        if name=="two_nominals" {assert_eq!(candidate.facts.type_holes.len(),2);assert_ne!(candidate.facts.type_holes[0].key,candidate.facts.type_holes[1].key);}
        assert!(pending::check_extraction(&candidate,&p).is_ok());
        let bytes=trust_ir::binary::serialize_template(t).unwrap();assert_eq!(trust_ir::binary::deserialize_template(&bytes).unwrap(),*t);
        let bindings=producer::template_metadata::rustc::owner_bindings(tcx,def.to_def_id()).unwrap();
        let arg_count=candidate.module.func_types[candidate.module.functions[0].ty.as_usize()].params.len() as u32;
        // Actual declaration identities only: no source-effect census or judgement.
        // Same established recipe as probes/callable_header.rs.
        let ledger=candidate.callees.iter().map(|c|{
         let mut ids=vec![];
         for definition in [c.site_def_id,c.def_id] {
          let hash=tcx.def_path_hash(definition);
          let stable=(hash.stable_crate_id().as_u64(),hash.local_hash().as_u64());
          if !ids.contains(&stable){ids.push(stable);}
         }
         assert!(c.site_args.is_none(),"generic fixture callee uses its checked typed hole");
         let hole=candidate.facts.callee_holes.iter().find(|hole|hole.decl==c.func_id).expect("every actual fixture declaration has a typed callee hole");
         let HoleKey::Callee{item,..}=&hole.key else{panic!("actual declaration must retain its typed callee key")};
         assert_eq!(ids.as_slice(),std::slice::from_ref(item));
         entry::EvidenceLedgerRow{func_id:c.func_id.index(),ids,site:None}
        }).collect();
        let non_authoritative=entry::encode_evidence(&entry::Evidence{arg_count,arg_enum:vec![false;arg_count as usize],ledger,..Default::default()});
        let frame=producer::template_metadata::frame(&bindings,t,tcx.sess.overflow_checks(),&non_authoritative).unwrap();
        if tuple_case(&name) {
         let other_name=if name=="tuple_identity" {"tuple_forward"} else {"tuple_identity"};
         let other=tcx.hir_body_owners().find(|d|tcx.opt_item_name(d.to_def_id()).is_some_and(|n|n.as_str()==other_name)).unwrap();
         let other_bindings=producer::template_metadata::rustc::owner_bindings(tcx,other.to_def_id()).unwrap();
         assert!(producer::template_metadata::read(&frame,&other_bindings,tcx.sess.overflow_checks()).is_err());
         row["other_actual_owner_refused"]=json!(true);
        }
        if candidate.facts.callee_holes.is_empty() || tuple_case(&name) {captured.0.insert(def.to_def_id(),frame);}
        row["template"]=json!(format!("{t:?}"));row["canonical_source_type_hole"]=json!(!tuple_case(&name));
        row["type_holes"]=json!(candidate.facts.type_holes.len());row["callee_holes"]=json!(candidate.facts.callee_holes.len());
        if !candidate.facts.type_holes.is_empty() {
         let mut hostile=candidate.clone();hostile.facts.type_holes[0].dependencies.clear();
         assert!(pending::assemble(&hostile,&Names(tcx,def.to_def_id()),name.clone()).is_err());
         hostile=candidate.clone();hostile.facts.type_holes[0].id=trust_ir::HoleId::new(99);
         assert!(pending::assemble(&hostile,&Names(tcx,def.to_def_id()),name.clone()).is_err());
         hostile=candidate.clone();hostile.facts.owner=None;
         assert!(pending::assemble(&hostile,&Names(tcx,def.to_def_id()),name.clone()).is_err());
         row["hostile_owner_argument_and_id_controls"]=json!(true);
        } else {assert!(tuple_case(&name));}
        if name=="with_lifetime" {assert_eq!(candidate.facts.parameter_indices,vec![1,2]);}
        if name=="tuple_lifetime" {assert_eq!(candidate.facts.parameter_indices,vec![1]);}
        if name=="tuple_forward" {assert_eq!(candidate.facts.callee_holes.len(),1);}
        if name.starts_with("relay") {
          assert_eq!(candidate.facts.callee_holes.len(),1);
          assert_ne!(candidate.facts.type_holes[0].id,candidate.facts.callee_holes[0].id);
          assert!(matches!(t.header.holes[candidate.facts.callee_holes[0].id.as_usize()].kind,HoleKind::Callee{decl} if decl==candidate.facts.callee_holes[0].decl));
        }
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
  for name in ["identity","bytes","with_lifetime","relay","relay_twice","nominal","nominal_enum","nominal_array","two_nominals"] {
   let row=rows.iter().find(|r|r["name"]==name).unwrap();assert_eq!(row["canonical_source_type_hole"],true,"{row:#}");
  }
  for name in ["inspect","nominal_field","nominal_construct","nominal_union"] {
   let row=rows.iter().find(|r|r["name"]==name).unwrap();assert!(row.get("capture_refusal").is_some()||row.get("assembly_refusal").is_some(),"{row:#}");
  }
  let ground=rows.iter().find(|r|r["name"]=="ground_nominal").unwrap();
  assert_eq!(ground["unchanged_ground_template_control"],true);
  assert_eq!(ground["baseline_same_owner_and_module"],true);
  assert_eq!(ground["unused_original_type_parameter"],true);
  assert_eq!(ground["header_identity"],"ground_nominal");
  assert_eq!(ground["type_holes"],0);assert_eq!(ground["header_type_holes"],0);
  assert_eq!(ground["canonical_source_type_hole"],false);
  assert_eq!(ground["production_refusal"],"conservation-unchecked");
  assert_eq!(ground["entry_bytes"],false);assert_eq!(ground["proof_authority"],false);
  for name in ["tuple_identity","tuple_nested","tuple_forward","tuple_two_types","tuple_lifetime"] {
   let row=rows.iter().find(|r|r["name"]==name).unwrap();assert_eq!(row["canonical_structural_tuple"],true,"{row:#}");
   assert_eq!(row["actual_owner_argument_and_type_controls"],true);assert_eq!(row["other_actual_owner_refused"],true);
  }
  assert_eq!(rows.iter().find(|r|r["name"]=="fixed").unwrap()["capture"],"not generic");
  assert_eq!(rows.len(),20,"all15original and5tuple owners remain in the probe");
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
      assert_eq!(image.roots().len(),1);assert!(matches!(image.roots()[0],trust_ir::Ty::Array(_, _)|trust_ir::Ty::Struct(_)|trust_ir::Ty::Enum(_)));
      let source_key=producer::template_key::decode(&hole.key).unwrap();let HoleKey::Type(key)=source_key else{unreachable!()};
      let original=producer::template_key::rustc::ty_of_key(tcx,&key,owner).unwrap();
      let direct=producer::concrete_type_transport::lower(tcx,instance,&[original]).unwrap();
      assert_eq!(image.roots(),direct.roots());assert_eq!(image.module().stable_digest(),direct.module().stable_digest());
     }
     let graph=producer::template_metadata::instantiate::construct_with(tcx,instance,&mut captured).unwrap();
     if name=="tuple_forward" {assert_eq!(graph.callables().len(),2);} else {assert_eq!(graph.callables().len(),1);}
     let header=&graph.callables()[0];assert_eq!(header.instance(),instance);
     let actual=tcx.fn_abi_of_instance(rustc_middle::ty::TypingEnv::fully_monomorphized().as_query_input((instance,rustc_middle::ty::List::empty()))).unwrap();
     assert!(std::ptr::eq(actual,header.fn_abi()));header.validate(graph.module()).unwrap();
     assert!(graph.module().functions.iter().all(|f|f.body_gate==Some(trust_ir::BodyGate::Ungated)));
     assert!(graph.module().proof_obligations.is_empty()&&graph.module().proof_certificates.is_empty());
     assert!(graph.source_checks().is_none(),"S1 fixture has no retained source capsule");
     if tuple_case(&name) {
      let original=tuple_sources[&owner];
      let key=producer::template_key::rustc::checked_type_key(tcx,original,owner).unwrap();
      let encoded=producer::template_key::encode(&HoleKey::Type(key)).unwrap();
      let image=producer::concrete_type_transport::from_key(tcx,instance,&encoded).unwrap();
      let direct=producer::concrete_type_transport::lower(tcx,instance,&[original]).unwrap();
      assert_eq!(image.roots(),direct.roots());assert_eq!(image.module().stable_digest(),direct.module().stable_digest());
      assert!(matches!(image.roots(),[trust_ir::Ty::Tuple(_)]));assert!(!image.module().tuple_layouts.is_empty());
      for callable in graph.callables() {
       let actual=tcx.fn_abi_of_instance(rustc_middle::ty::TypingEnv::fully_monomorphized().as_query_input((callable.instance(),rustc_middle::ty::List::empty()))).unwrap();
       assert!(std::ptr::eq(actual,callable.fn_abi()));callable.validate(graph.module()).unwrap();
      }
      if name=="tuple_two_types" {let body=graph.module().function_by_id(graph.entry()).unwrap();let sig=graph.module().func_type(body.ty).unwrap();assert_ne!(sig.params[0],sig.params[1],"tuple field order must preserve the actual instantiated signature");}
     }
     if name=="two_nominals" {let body=graph.module().function_by_id(graph.entry()).unwrap();let signature=graph.module().func_type(body.ty).unwrap();assert_ne!(signature.params[0],signature.params[1],"distinct actual nominal definitions may not alias by field shape");}
     constructions.push(json!({"owner":name,"actual_args":format!("{args:?}"),"tuple_passthrough":tuple_case(&name),"actual_callable_count":graph.callables().len(),"actual_captured_key_concrete_image_matches":true,"constructed_ungated":true,"actual_fnabi_bound":true,"source_bound":false,"proof_authority":false}));
    }
   }
  }
  assert_eq!(constructions.iter().filter(|r|r["tuple_passthrough"]==false).count(),8,"all old construction cases remain");
  assert_eq!(constructions.iter().filter(|r|r["tuple_passthrough"]==true).count(),6,"all new tuple call sites remain");
  assert_eq!(constructions.len(),14);assert!(constructions.iter().all(|r|r["actual_captured_key_concrete_image_matches"]==true));
  rows.push(json!({"constructions":constructions,"source_evidence":"deliberately non-authoritative fixture bytes","proof_authority":false,"runtime_type_hole":false}));
  println!("{}",serde_json::to_string_pretty(&rows).unwrap());
  rustc_driver::Compilation::Stop
 }
}
fn main(){
    // FIRST native-main operation: preserve original SDK/GNU descriptor identity.
    if let Err(error) = unsafe { rustc_data_structures::jobserver::capture_early() } {
        eprintln!("embedded compiler early custody refused: {error}");
        std::process::exit(75);
    }
let mut args:Vec<_>=std::env::args().collect();args.push("-Zno-steal-thir".into());rustc_driver::run_compiler(&args,&mut Observer);}
