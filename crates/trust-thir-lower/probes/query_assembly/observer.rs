#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_data_structures;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate trust_thir_lower;
extern crate trust_mir_extract;
extern crate trust_ir_build;
extern crate trust_ir;

struct Observe {
 captured: Option<(trust_thir_lower::Lowered, Option<String>)>,
 confirmed_clone: bool,
}
impl rustc_driver::Callbacks for Observe {
 fn after_expansion<'tcx>(&mut self, _: &rustc_interface::interface::Compiler,
  tcx: rustc_middle::ty::TyCtxt<'tcx>) -> rustc_driver::Compilation {
  let owners: Vec<_> = tcx.hir_body_owners().filter(|d| tcx.def_path_str(*d).ends_with("MonadInst::uv")).collect();
  assert_eq!(owners.len(), 1, "exact unchanged original owner");
  let owner=owners[0];
  eprintln!("EXACT ORIGINAL OWNER {}", tcx.def_path_str(owner));
  let (body, root) = tcx.thir_body(owner).unwrap();
  let body=body.borrow();
  let _freeze=trust_thir_lower::enter_mir_built_ctfe_freeze(owner);
  let (lowered, drop)=trust_thir_lower::lower_module_from_thir_for_query(tcx,owner,&body,root);
  std::mem::drop(_freeze);
  std::mem::drop(body);
  assert!(matches!(trust_thir_lower::crate_module::assemble_query_body(tcx,owner,(lowered.clone(),None)),Err(trust_thir_lower::crate_module::QueryAssemblyRefusal::AnalysisNotCompleted)),"missing genuine analysis cache must refuse without forcing analysis");
  self.captured=Some((lowered,drop));
  // The THIR borrow and simulated MIR-building freeze end before ordinary analysis.
  rustc_driver::Compilation::Continue
 }
 fn after_analysis<'tcx>(&mut self, _: &rustc_interface::interface::Compiler,
  tcx: rustc_middle::ty::TyCtxt<'tcx>) -> rustc_driver::Compilation {
  let owners: Vec<_> = tcx.hir_body_owners().filter(|d| tcx.def_path_str(*d).ends_with("MonadInst::uv")).collect();
  assert_eq!(owners.len(),1);
  let owner=owners[0];
  let (lowered,drop)=self.captured.take().expect("unchanged body captured before analysis");
  {
    let _freeze=trust_thir_lower::enter_mir_built_ctfe_freeze(owner);
    assert!(matches!(trust_thir_lower::crate_module::assemble_query_body(tcx,owner,(lowered.clone(),None)),Err(trust_thir_lower::crate_module::QueryAssemblyRefusal::ActiveMirBuilding)));
  }
  let errors=trust_ir_build::validate_module(&lowered.module);
  let mut violations=Vec::new();
  lowered.module.visit_storage_violations(&lowered.module.layout_table(),|v|violations.push(v));
  let out=std::path::PathBuf::from(std::env::var_os("TRUST_UV_CAPTURE_DIRECTORY").expect("owned output required"));
  std::fs::write(out.join("original-uv.module.debug"),format!("{:#?}",lowered.module)).unwrap();
  eprintln!("ORIGINAL UV unsupported={:?} drop={drop:?} opaque={} symbolic={} contains_call={}",lowered.unsupported,lowered.opaque_collapse,lowered.symbolic,lowered.contains_call);
  eprintln!("ORIGINAL UV validation={errors:?}");
  eprintln!("ORIGINAL UV storage={violations:?}");
  eprintln!("ORIGINAL UV enum_declines={:?}",lowered.enum_declines);
  assert!(lowered.unsupported.is_empty() && drop.is_none() && !lowered.opaque_collapse && !lowered.symbolic && violations.is_empty());
  let rejects = |candidate| match trust_thir_lower::crate_module::assemble_query_body(tcx,owner,(candidate,None)) {
    Err(_) => true,
    Ok(outcome) => !trust_ir_build::validate_module(outcome.module()).is_empty(),
  };
  let mut bad_id=lowered.clone();bad_id.module.functions[0].id=trust_ir::FuncId::new(9);
  assert!(rejects(bad_id),"altered caller id cannot assemble");
  let mut missing=lowered.clone();missing.callees.clear();
  assert!(rejects(missing),"omitted real callee ledger cannot assemble valid calls");
  let mut conflict=lowered.clone();conflict.callees[0].ret_ty_conflict=true;
  assert!(rejects(conflict),"conflicting return standing cannot assemble valid returned values");
  let mut withdrawn=lowered.clone();withdrawn.callees[0].params.withdraw();
  assert!(rejects(withdrawn),"withdrawn parameter standing cannot be resurrected");
  let mut malformed=lowered.clone();
  let field=malformed.module.structs.iter_mut().flat_map(|s|s.fields.iter_mut()).find(|f|matches!(f.ty,trust_ir::Ty::Storage(_))).expect("actual source storage");
  field.ty=trust_ir::Ty::Storage(trust_ir::StorageLayout::new(3,8));
  assert!(matches!(
    trust_thir_lower::crate_module::assemble_query_body(tcx,owner,(malformed,None)),
    Err(trust_thir_lower::crate_module::QueryAssemblyRefusal::UnencodableBody(
      trust_ir::BinaryProjectionError::InvalidStorageGeometry(_)
    ))
  ),"invalid storage geometry must refuse before lineage encoding");
  let mut bad_table=lowered.clone();bad_table.module.structs[0].id=trust_ir::StructId::new(99);
  assert!(rejects(bad_table),"nonpositional struct metadata cannot assemble");
  assert!(trust_thir_lower::crate_module::assemble_query_body(tcx,owner,(lowered.clone(),Some("actual-test-drop-refusal".into()))).is_err(),"drop refusal cannot be erased");
  eprintln!("QUERY ASSEMBLY NEGATIVES PASS: caller-id, missing-ledger, return-conflict, withdrawn-params, malformed-wire, bad-table, drop-refusal");
  let assembled=trust_thir_lower::crate_module::assemble_query_body(tcx,owner,(lowered.clone(),drop)).expect("canonical unpublished query assembly");
  eprintln!("QUERY ASSEMBLY entry={:?} declarations={} original_callees={:?}",assembled.entry(),assembled.declaration_count(),assembled.original_callees());
  assert_eq!(assembled.declaration_count(),1);
  assert_eq!(assembled.original_callees().len(), 1);
  let callee = &assembled.original_callees()[0];
  if self.confirmed_clone {
    use rustc_middle::ty;
    assert!(lowered.contains_call && lowered.enum_declines.is_empty());
    assert!(callee.is_local && !callee.force_havoc && callee.concrete_key.is_some());
    assert!(callee.instance_args.as_ref().is_some_and(Vec::is_empty));
    assert_ne!(callee.site_def_id, callee.def_id);
    assert_eq!(tcx.trait_item_of(callee.def_id), Some(callee.site_def_id));
    let clone_trait = tcx.lang_items().clone_trait().expect("actual Clone lang item");
    assert_eq!(tcx.trait_of_assoc(callee.site_def_id), Some(clone_trait));
    let clone_impl = tcx.trait_impl_of_assoc(callee.def_id).expect("actual Clone impl owner");
    let clone_ref = tcx.impl_trait_ref(clone_impl).instantiate_identity().skip_normalization();
    assert_eq!(clone_ref.def_id, clone_trait);
    let self_ty = clone_ref.self_ty();
    assert!(matches!(self_ty.kind(), ty::Adt(def, _) if def.is_enum()));
    let parent_impl = tcx.inherent_impl_of_assoc(owner.to_def_id()).expect("original inherent impl");
    let parent_ty = tcx.type_of(parent_impl).instantiate_identity().skip_normalization();
    let ty::Adt(parent, args) = parent_ty.kind() else { panic!("original parent ADT") };
    let fields: Vec<_> = parent.non_enum_variant().fields.iter()
      .filter(|f| matches!(f.name.as_str(), "u" | "v")).collect();
    assert_eq!(fields.len(), 2);
    assert!(fields.iter().all(|f| f.ty(tcx, *args).skip_normalization() == self_ty));
    let module = assembled.module();
    let entry = module.functions.iter().find(|f| f.id == assembled.entry()).expect("entry body");
    let declaration = module.functions.iter().find(|f| f.id != assembled.entry()).expect("Clone declaration");
    assert!(declaration.blocks.is_empty(), "bounded query assembly supplies no executable Clone body");
    assert_eq!(declaration.name.as_str(), tcx.symbol_name(ty::Instance::mono(tcx, callee.def_id)).name);
    let calls = entry.blocks.iter().flat_map(|b| &b.body).filter(|node| matches!(
      &node.inst,
      trust_ir::Inst::Call { callee, .. } | trust_ir::Inst::CallCannotUnwind { callee, .. }
      if *callee == declaration.id
    )).count();
    assert_eq!(calls, 2, "both original field clones target the actual declared implementation");
    eprintln!("ACTUAL CONCRETE CLONE {:?}: two calls, canonical symbol, bodyless declaration", callee.def_id);
  } else {
    assert!(callee.force_havoc && callee.concrete_key.is_none());
  }
  let target=assembled.module().target_info.clone().expect("actual target stamped");
  assert_eq!(target.pointer_size,u32::from(tcx.sess.target.pointer_width/8));
  let mut bad_target=lowered.clone();bad_target.module.target_info=Some(target);
  bad_target.module.target_info.as_mut().unwrap().pointer_size=1;
  assert!(rejects(bad_target),"contradictory target facts cannot be retained or overwritten");
  eprintln!("QUERY ASSEMBLY phase, withdrawal, geometry and target negatives PASS");
  let completed_errors=trust_ir_build::validate_module(assembled.module());
  std::fs::write(out.join("assembled.module.debug"),format!("{:#?}",assembled.module())).unwrap();
  eprintln!("QUERY ASSEMBLY validation={completed_errors:?}");
  assert!(completed_errors.is_empty(),"canonical bounded assembly validation");
  eprintln!("VALID UNPUBLISHED QUERY MODULE; concrete_clone={}; no executable Clone or proof grade", self.confirmed_clone);
  rustc_driver::Compilation::Stop
 }
}
fn main() {
 unsafe {rustc_data_structures::jobserver::capture_early().expect("early jobserver")};
 eprintln!("ACTUAL CURRENT DRIVER {}",rustc_interface::util::rustc_version_str().unwrap());
 let mut args: Vec<_> = std::env::args().collect();
 let confirmed_clone = args.get(1).is_some_and(|a| a == "--expect-concrete-clone");
 if confirmed_clone { args.remove(1); }
 rustc_driver::run_compiler(&args, &mut Observe { captured: None, confirmed_clone });
}
