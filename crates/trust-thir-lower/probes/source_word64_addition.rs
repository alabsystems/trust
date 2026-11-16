#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_data_structures;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_hir;
extern crate rustc_span;
extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_attr_ir;
extern crate trust_thir_lower;
extern crate rust_source_word64_capture;
extern crate trust_ir;
extern crate trust_ir_build;
extern crate serde_json;
use serde_json::json;
use rustc_middle::ty;
fn source_hash(tcx:ty::TyCtxt<'_>,span:rustc_span::Span)->serde_json::Value {
 if span.is_dummy(){return json!({"dummy":true})}
 let f=tcx.sess.source_map().lookup_source_file(span.lo());json!({"file":format!("{:?}",f.name),"hash":f.src_hash.to_string(),"span":format!("{span:?}")})
}
// Read the actual crate-store envelope for this resolved callee. The original
// bytes and decoded body are evidence INPUTS, not an upstream-admission token
// or a Rust-source TV theorem. No caller-supplied body or owner is substituted.
fn retain_callee_entry(
 tcx:ty::TyCtxt<'_>,callee:rustc_span::def_id::DefId,
 out:&std::path::Path,expression:usize,
)->serde_json::Value {
 let Some(blob)=tcx.trust_ir_entry(callee) else {
  return json!({"retained":false,"reason":"actual loaded crate has no entry for this callee"})
 };
 let envelope_name=format!("callee-{expression}-original-entry.bin");
 std::fs::write(out.join(&envelope_name),&blob.0).unwrap();
 let Some(header)=tcx.trust_ir_crate_header(callee.krate) else {
  return json!({"retained":false,"envelope":envelope_name,"reason":"actual crate header absent"})
 };
 if header.trust_ir_version!=trust_ir::binary::VERSION
  ||header.entry_schema!=trust_thir_lower::rmeta_entry::ENTRY_SCHEMA
  ||header.crate_refusal.is_some() {
  return json!({"retained":false,"envelope":envelope_name,"reason":"actual crate producer header refused"})
 }
 let entry=match trust_thir_lower::rmeta_entry::decode_entry_for_overflow(
  &blob.0,tcx.sess.overflow_checks(),
 ) {
  Ok(entry)=>entry,
  Err(reason)=>return json!({"retained":false,"envelope":envelope_name,"reason":format!("{reason}")}),
 };
 let hash=tcx.def_path_hash(callee);
 let expected=trust_thir_lower::rmeta_entry::EntryBinding {
  stable_crate_id:tcx.stable_crate_id(callee.krate).as_u64(),
  local_hash:hash.local_hash().as_u64(),
 };
 if entry.binding!=expected {
  return json!({"retained":false,"envelope":envelope_name,"reason":"entry differs from actual resolved Rust owner"})
 }
 let module_name=format!("callee-{expression}-decoded-module.bin");
 let bytes=trust_ir::binary::serialize_module(&entry.module).unwrap();
 std::fs::write(out.join(&module_name),&bytes).unwrap();
 std::fs::write(out.join(format!("callee-{expression}-decoded-module.debug")),format!("{:#?}",entry.module)).unwrap();
 json!({"retained":true,"envelope":envelope_name,"decoded_module":module_name,
  "binding":format!("{:?}",entry.binding),"overflow_checks":entry.overflow_checks,
  "envelope_digest":format!("{:?}",entry.content_digest),"module_digest":format!("{:?}",entry.digest),
  "function_count":entry.module.functions.len(),
  "defined_count":entry.module.functions.iter().filter(|f| !f.is_declaration()).count(),
  "declaration_count":entry.module.functions.iter().filter(|f| f.is_declaration()).count(),
  "validator":format!("{:?}",trust_ir_build::validate_module(&entry.module)),
  "scope":"Actual resolved-owner-bound metadata envelope and decoded module DATA only; no strict upstream admission, source TV, source semantics, ABI, NoUB, byte proof or codegen authority."})
}

// External qualification data only. This is not a compiler admission capability.
fn closed_profile<'tcx>(
 tcx:ty::TyCtxt<'tcx>,def:rustc_span::def_id::LocalDefId,
 thir:&rustc_middle::thir::Thir<'tcx>,root:rustc_middle::thir::ExprId,
)->Result<serde_json::Value,String>{
 use rustc_middle::thir::{ExprKind,PatKind,BlockSafety};
 let refuse=|s:&str|s.to_owned();
 let sig=tcx.fn_sig(def.to_def_id()).instantiate_identity().skip_binder();
 if sig.inputs()!=[tcx.types.u64] ||sig.output()!=tcx.types.u64 ||sig.c_variadic()
  ||sig.safety()!=rustc_hir::Safety::Safe ||sig.abi()!=rustc_abi::ExternAbi::Rust
  ||(tcx.generics_of(def).count()!=0 ||tcx.generics_of(def).parent.is_some()){
  return Err(refuse("exact closed safe Rust U64 signature, no generics"))
 }
 // Inline hints change optimization, not this source value equation. No other
 // attribute is part of this bounded diagnostic source profile.
 if tcx.get_all_attrs(def.to_def_id()).iter().any(|a| !matches!(a,rustc_attr_ir::Attribute::Parsed(rustc_attr_ir::AttributeKind::Inline(..)))){
  return Err(refuse("exact closed safe Rust U64 signature, no attributes/generics"))
 }
 if thir.params.len()!=1 ||thir.blocks.len()!=1 ||!thir.stmts.is_empty(){return Err(refuse("complete parameter/block/statement population"))}
 let parameter=thir.params.iter().next().unwrap();
 let pat=parameter.pat.as_ref().ok_or_else(||refuse("explicit parameter"))?;
 let PatKind::Binding{var,subpattern:None,..}=pat.kind else{return Err(refuse("single original binding"))};
 if parameter.ty!=tcx.types.u64 ||pat.ty!=tcx.types.u64{return Err(refuse("actual parameter type"))}
 let mut used=std::collections::BTreeSet::new();
 let mut peel=|mut id:rustc_middle::thir::ExprId|->Result<rustc_middle::thir::ExprId,String>{
  loop {
   if !used.insert(format!("{id:?}")){return Err(refuse("repeated original node"))}
   if let ExprKind::Scope{value,..}=thir.exprs[id].kind {id=value}else{return Ok(id)}
  }
 };
 let outer=peel(root)?;
 let ExprKind::Block{block}=thir.exprs[outer].kind else{return Err(refuse("original function block"))};
 let body=&thir.blocks[block];
 if body.targeted_by_break ||!body.stmts.is_empty() ||!matches!(body.safety_mode,BlockSafety::Safe){return Err(refuse("safe closed block"))}
 let call=peel(body.expr.ok_or_else(||refuse("original tail"))?)?;
 let ExprKind::Call{fun,ref args,from_hir_call:true,..}=thir.exprs[call].kind else{return Err(refuse("original resolved call"))};
 if args.len()!=2 ||thir.exprs[call].ty!=tcx.types.u64{return Err(refuse("actual call result/arity"))}
 let fun=peel(fun)?;
 if !matches!(thir.exprs[fun].kind,ExprKind::ZstLiteral{..}){return Err(refuse("effect-free original function item"))}
 let ty::FnDef(callee,generic)=*thir.exprs[fun].ty.kind() else{return Err(refuse("actual FnDef"))};
 let model=trust_thir_lower::core_u64_wrapping_add_model_v1(tcx,callee,generic.skip_binder()).ok_or_else(||refuse("authenticated versioned primitive model"))?;
 let receiver=peel(args[0])?;
 if !matches!(thir.exprs[receiver].kind,ExprKind::VarRef{id} if id==var) ||thir.exprs[receiver].ty!=tcx.types.u64{return Err(refuse("same original parameter identity"))}
 let literal_node=peel(args[1])?;
 if matches!(thir.exprs[literal_node].kind,ExprKind::VarRef{id} if id==var) {
  if thir.exprs[literal_node].ty!=tcx.types.u64 ||used.len()!=thir.exprs.len(){return Err(refuse("complete original expression population/types"))}
  return Ok(json!({"accepted":true,"source_operation":"word64-self-addition","function_name":tcx.item_name(def.to_def_id()).to_string(),"parameter_identity":format!("{var:?}"),"receiver_node":format!("{receiver:?}"),"argument_node":format!("{literal_node:?}"),"actual_call_node":format!("{call:?}"),"actual_callee":format!("{callee:?}"),"model":model,"full_original_expression_count":used.len(),"scope":"Typed original source-node DATA only; no source/IR theorem, core-wrapper correspondence, NoUB, ABI, admission or proof grade."}))
 }
 // Keep the original literal experiment's attribute-free source grammar.
 if !tcx.get_all_attrs(def.to_def_id()).is_empty(){return Err(refuse("literal source attributes"))}
 let ExprKind::Literal{lit,neg:false}=thir.exprs[literal_node].kind else{return Err(refuse("original nonnegative integer literal or same parameter"))};
 let rustc_ast::LitKind::Int(value,_)=lit.node else{return Err(refuse("original integer literal"))};
 let literal=u64::try_from(value.get()).map_err(|_|refuse("literal full U64 bounds"))?;
 if thir.exprs[literal_node].ty!=tcx.types.u64 ||used.len()!=thir.exprs.len(){return Err(refuse("complete original expression population/types"))}
 Ok(json!({"accepted":true,"source_operation":"word64-literal-addition","function_name":tcx.item_name(def.to_def_id()).to_string(),"parameter_identity":format!("{var:?}"),"literal":literal,"literal_node":format!("{literal_node:?}"),"actual_call_node":format!("{call:?}"),"actual_callee":format!("{callee:?}"),"model":model,"full_original_expression_count":used.len(),"scope":"Typed original source-node DATA; versioned core-wrapper semantic correspondence remains an explicit model premise. No source-refinement/NoUB/admission authority."}))
}

struct Observer;
impl rustc_driver::Callbacks for Observer {
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:ty::TyCtxt<'tcx>)->rustc_driver::Compilation {
  let out=std::path::PathBuf::from(std::env::var("TRUST_ACTUAL_ADDITION_OUT").expect("owned output"));
  let mut defs:Vec<_>=tcx.hir_body_owners().collect();defs.sort_by_key(|d|tcx.def_path_str(*d));
  let all:Vec<_>=defs.iter().map(|d|json!({"owner":format!("{d:?}"),"path":tcx.def_path_str(*d),"kind":format!("{:?}",tcx.def_kind(d.to_def_id()))})).collect();
  let selected_name=std::env::var("TRUST_ACTUAL_ADDITION_FUNCTION").unwrap_or_else(|_|"addition".into());
  let selected:Vec<_>=defs.into_iter().filter(|d|tcx.opt_item_name(d.to_def_id()).is_some_and(|n|n.as_str()==selected_name)).collect();assert_eq!(selected.len(),1,"complete selected original owner");
  let def=selected[0];let sig=tcx.fn_sig(def.to_def_id()).instantiate_identity().skip_binder();
  let (thir,root)=tcx.thir_body(def).unwrap();assert!(!thir.is_stolen());let thir=thir.borrow();
  // Independent source capture happens before the probe reads any output IR.
  // Keep the actual borrowed snapshot alive through the later query assembly.
  let original_source_snapshot=rust_source_word64_capture::source_word64::capture(tcx,def);
  let source_snapshot=match &original_source_snapshot {
   Ok(snapshot)=>{
    use rust_source_word64_capture::source_word64::{Expression,Operand};
    let operand=|value:&Operand|match value {
     Operand::Parameter(index)=>json!({"kind":"parameter","index":index}),
     Operand::Literal(value)=>json!({"kind":"literal","value":value}),
    };
    let expression=match snapshot.expression() {
     Expression::Operand{expression,value}=>json!({"kind":"operand","source_expression":expression,"value":operand(value)}),
     Expression::Call(call)=>json!({"kind":format!("{:?}",call.kind()),"source_expression":call.expression(),"definition":format!("{:?}",tcx.def_path_hash(call.definition())),"arguments":format!("{:?}",call.arguments()),"operands":call.operands().iter().map(|(id,value)|json!({"source_expression":id,"value":operand(value)})).collect::<Vec<_>>()}),
    };
    // Transport must preserve the actual original observation; decoding a claim
    // does not recreate the borrowed TCX snapshot or confer proof authority.
    use rust_source_word64_capture::source_word64::record;
    let retained=snapshot.to_record().expect("actual source record export");
    let wire=record::encode(&retained).expect("bounded source record encoding");
    assert_eq!(record::decode(&wire).expect("source claim decoding"),retained);
    for end in 0..wire.len() { assert!(record::decode(&wire[..end]).is_err()); }
    let owner=tcx.def_path_hash(def.to_def_id());
    assert_eq!(retained.owner.stable_crate_id,owner.stable_crate_id().as_u64());
    assert_eq!(retained.owner.local_hash,owner.local_hash().as_u64());
    assert_eq!(retained.expressions as usize,thir.exprs.len());
    let source_record=json!({"schema":record::SCHEMA,"bytes":wire.len(),"roundtrip":true,"every_truncation_refused":true,"owner_matches_original":true,"claim_only":true});
    let other=tcx.hir_body_owners().find(|owner|*owner!=def);
    json!({"captured":true,"source_record":source_record,"belongs_to_actual_owner":snapshot.belongs_to(tcx,def),"rejects_other_owner":other.map(|owner|!snapshot.belongs_to(tcx,owner)),"parameters":snapshot.parameters().iter().map(|id|format!("{id:?}")).collect::<Vec<_>>(),"original_expressions":snapshot.original_expressions(),"source_hash":snapshot.source_file().src_hash.to_string(),"expression":expression,"scope":"Actual original TCX source data only; no Rust source TV, purity, termination, ABI, NoUB or admission."})
   }
   Err(reason)=>json!({"captured":false,"reason":reason.to_string()}),
  };
  let mut calls=vec![];let mut exprs=vec![];
  for (index,e) in thir.exprs.iter().enumerate(){
   exprs.push(json!({"id":index,"type":format!("{:?}",e.ty),"kind":format!("{:?}",e.kind),"span":format!("{:?}",e.span),"source":tcx.sess.source_map().span_to_snippet(e.span).ok()}));
   if let rustc_middle::thir::ExprKind::Call{fun,..}=e.kind {
    if let ty::FnDef(callee,args)=*thir.exprs[fun].ty.kind(){
     if callee.is_local() {
      calls.push(json!({"callee":format!("{callee:?}"),"path":tcx.def_path_str(callee),"def_path_hash":format!("{:?}",tcx.def_path_hash(callee)),"crate_name":tcx.crate_name(callee.krate).to_string(),"selected_primitive_model":trust_thir_lower::core_u64_wrapping_add_model_v1(tcx,callee,args.skip_binder()),"loaded_source_paths":[],"signature":format!("{:?}",tcx.fn_sig(callee).instantiate(tcx,args.skip_binder()).skip_binder())}));
      continue;
     }
     let loaded=tcx.used_crate_source(callee.krate);
     let core_root=rustc_span::def_id::DefId{krate:callee.krate,index:rustc_span::def_id::CRATE_DEF_INDEX};
     let intrinsic_module=tcx.module_children(core_root).iter().find(|c|c.ident.name.as_str()=="intrinsics").and_then(|c|c.res.opt_def_id());
     let intrinsic=intrinsic_module.and_then(|m|tcx.module_children(m).iter().find(|c|c.ident.name.as_str()=="wrapping_add").and_then(|c|c.res.opt_def_id()));
     let intrinsic_facts=intrinsic.map(|id|json!({"id":format!("{id:?}"),"path":tcx.def_path_str(id),"builtin":format!("{:?}",tcx.intrinsic(id)),"source":source_hash(tcx,tcx.def_span(id))}));
     let retained_entry=retain_callee_entry(tcx,callee,&out,index);
     calls.push(json!({"retained_entry":retained_entry,"callee":format!("{callee:?}"),"path":tcx.def_path_str(callee),"def_path_hash":format!("{:?}",tcx.def_path_hash(callee)),"crate_name":tcx.crate_name(callee.krate).to_string(),"crate_hash":format!("{:?}",tcx.crate_hash(callee.krate)),"stable_crate_id":format!("{:?}",tcx.stable_crate_id(callee.krate)),"loaded_source_paths":loaded.paths().map(|p|p.display().to_string()).collect::<Vec<_>>(),"signature":format!("{:?}",tcx.fn_sig(callee).instantiate(tcx,args.skip_binder()).skip_binder()),"selected_primitive_model":trust_thir_lower::core_u64_wrapping_add_model_v1(tcx,callee,args.skip_binder()),"intrinsic":format!("{:?}",tcx.intrinsic(callee)),"parent":format!("{:?}",tcx.parent(callee)),"parent_kind":format!("{:?}",tcx.def_kind(tcx.parent(callee))),"def_span":format!("{:?}",tcx.def_span(callee)),"definition_source":tcx.sess.source_map().span_to_snippet(tcx.def_span(callee)).ok(),"actual_args":format!("{args:?}"),"core_sized_crate":tcx.lang_items().sized_trait().map(|d|format!("{:?}",d.krate)),"def_source_hash":source_hash(tcx,tcx.def_span(callee)),"callsite_source_hash":source_hash(tcx,tcx.def_span(callee).source_callsite()),"core_root_source_hash":source_hash(tcx,tcx.def_span(core_root)),"parent_source_hash":source_hash(tcx,tcx.def_span(tcx.parent(callee))),"parent_callsite_source_hash":source_hash(tcx,tcx.def_span(tcx.parent(callee)).source_callsite()),"core_intrinsic":intrinsic_facts}));
    }
   }
  }
  let source_profile=match closed_profile(tcx,def,&thir,root){Ok(p)=>p,Err(reason)=>json!({"accepted":false,"reason":reason})};
  // The historical profile stays literal-only. New source data must never
  // turn an old literal experiment's accepted bit green for self-addition.
  let profile=if source_profile["source_operation"]=="word64-self-addition" {
   json!({"accepted":false,"reason":"same-parameter addition is outside the literal profile"})
  }else{source_profile.clone()};
  let sourcefile=tcx.sess.source_map().lookup_source_file(tcx.def_span(def.to_def_id()).lo());
  let original_source=sourcefile.src.as_ref().expect("local original source retained").to_string();
  std::fs::write(out.join("original-source.rs"),&original_source).unwrap();
  // This calls the actual direct THIR query producer. No MIR producer,
  // synthesized module, instruction edits, ABI relabel or normalization follows.
  let (lowered,drop_refusal)=trust_thir_lower::lower_module_from_thir_for_query(tcx,def,&thir,root);
  let bytes=trust_ir::binary::serialize_module(&lowered.module).unwrap();
  std::fs::write(out.join("original-module.bin"),&bytes).unwrap();
  std::fs::write(out.join("original-module.debug"),format!("{:#?}",lowered.module)).unwrap();
  let report=json!({"scope":"ACTUAL direct THIR producer measurement/data only; no source/refinement/ABI/NoUB/admission/grade claim","all_local_owners":all,"source_snapshot":source_snapshot,"closed_profile":profile,"word64_source_profile":source_profile,"original_source_metadata_hash":sourcefile.src_hash.to_string(),"selected_owner":format!("{def:?}"),"selected_path":tcx.def_path_str(def),"owner_hash":format!("{:?}",tcx.def_path_hash(def.to_def_id())),"signature":format!("{sig:?}"),"hir_parameter_patterns":format!("{:?}",tcx.hir_body_owned_by(def).params),"root":format!("{root:?}"),"thir_exprs":exprs,"calls":calls,"binary_format_version":trust_ir::binary::FORMAT_VERSION,"module_stable_digest":format!("{:?}",lowered.module.stable_digest()),"unsupported":format!("{:?}",lowered.unsupported),"symbolic":lowered.symbolic,"opaque_collapse":lowered.opaque_collapse,"drop_refusal":drop_refusal,"validator":format!("{:?}",trust_ir_build::validate_module(&lowered.module)),"functions":lowered.module.functions.iter().map(|f|json!({"id":f.id.index(),"name":f.name,"calling_conv":format!("{:?}",f.calling_conv),"signature":format!("{:?}",lowered.module.func_type(f.ty)),"entry":f.entry.index(),"blocks":format!("{:?}",f.blocks)})).collect::<Vec<_>>()});
  std::fs::write(out.join("ACTUAL-THIR.json"),serde_json::to_vec_pretty(&report).unwrap()).unwrap();
  // Keep the raw query fragment above intact, including every validator error.
  // Canonical assembly is a SEPARATE structural image. Its bodyless callees
  // confer no implementation semantics, returned values, TV or admission.
  let assembled=match trust_thir_lower::crate_module::assemble_query_body(tcx,def,(lowered,drop_refusal)) {
   Ok(assembly)=>{
    let module=assembly.module();
    let bytes=trust_ir::binary::serialize_module(module).unwrap();
    std::fs::write(out.join("canonical-query-assembly.bin"),bytes).unwrap();
    json!({"assembled":true,"entry":assembly.entry().index(),"declarations":assembly.declaration_count(),"validator":format!("{:?}",trust_ir_build::validate_module(module)),"scope":"Canonical STRUCTURAL query assembly only; bodyless callees are not source/IR meaning or a closed executable proof subject."})
   }
   Err(reason)=>json!({"assembled":false,"reason":format!("{reason:?}")}),
  };
  std::fs::write(out.join("QUERY-ASSEMBLY.json"),serde_json::to_vec_pretty(&assembled).unwrap()).unwrap();
  rustc_driver::Compilation::Stop
 }
}
fn main(){
 // FIRST main operation: canonical inherited descriptor capture, before argv/fs.
 if let Err(error)=unsafe{rustc_data_structures::jobserver::capture_early()}{eprintln!("early custody refused: {error}");std::process::exit(75)}
 let mut args:Vec<_>=std::env::args().collect();args.push("-Zno-steal-thir".into());rustc_driver::run_compiler(&args,&mut Observer);
}
