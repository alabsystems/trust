//! Separate-process actual upstream Rust metadata/source-input probe. The S2
//! inputs came from real THIR and real pending lowering in the producer probe;
//! these owned sidecar files are not canonical rmeta publication or a new SDK.
#![feature(rustc_private)]
extern crate rustc_target;
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
extern crate trust_thir_lower;
extern crate trust_ir;
extern crate serde_json;
use rustc_middle::{ty::{self,TyCtxt},thir::ExprKind};
use trust_thir_lower::template_metadata::{self as meta,instantiate::{self,TemplateProvider}};
struct Provider{directory:std::path::PathBuf}
impl<'tcx> TemplateProvider<'tcx> for Provider{
 fn load(&mut self,tcx:TyCtxt<'tcx>,owner:rustc_span::def_id::DefId)->Result<meta::AuthenticatedTemplate,meta::MetadataError>{
  assert!(!owner.is_local(),"this probe must use actual external definitions");
  let expected=meta::rustc::owner_bindings(tcx,owner)?;
  let file=self.directory.join(format!("{:016x}-{:016x}.s2",expected.owner.0,expected.owner.1));
  let bytes=std::fs::read(file).map_err(|_|meta::MetadataError("missing retained upstream source image".into()))?;
  meta::read(&bytes,&expected,tcx.sess.overflow_checks())
 }
}
struct Probe;
impl rustc_driver::Callbacks for Probe{
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->rustc_driver::Compilation{
  let main=tcx.entry_fn(()).unwrap().0.expect_local();let(stored,_)=tcx.thir_body(main).unwrap();let thir=stored.borrow();
  let mut provider=Provider{directory:std::env::var_os("SOURCE_FACTS_DIR").unwrap().into()};let mut rows=Vec::new();let refusals:Vec<serde_json::Value>=Vec::new();
  for(_,expr)in thir.exprs.iter_enumerated(){
   let ExprKind::Call{fun,..}=&expr.kind else{continue};let ty::FnDef(def,args)=*thir[*fun].ty.kind()else{continue};
   let name=tcx.item_name(def).to_string();if !["root","source_chain","source_diamond","source_identity","source_const_array","source_typed_relay","source_value_chain"].contains(&name.as_str()){continue}
   assert!(!def.is_local());let instance=ty::Instance::try_resolve(tcx,ty::TypingEnv::fully_monomorphized(),def,args.skip_binder()).unwrap().unwrap();
   let artifact=provider.load(tcx,def).unwrap();let Some(meta::SourceRetention::Captured(source))=artifact.source()else{panic!()};
   let concrete=trust_thir_lower::effect_conservation::thir_source::concrete::instantiate(tcx,instance,source).unwrap();assert_eq!(concrete.instance(),instance);
   let result=instantiate::construct_source_checked_with(tcx,instance,&mut provider);
   let graph=result.unwrap();let records=graph.source_checks().unwrap();assert_eq!(records.len(),match name.as_str(){"root"|"source_typed_relay"|"source_value_chain"=>2,"source_chain"=>3,"source_diamond"=>4,_=>1});
   assert_eq!(graph.callables().len(),records.len());
   for callable in graph.callables(){let actual=tcx.fn_abi_of_instance(ty::TypingEnv::fully_monomorphized().as_query_input((callable.instance(),ty::List::empty()))).unwrap();assert!(std::ptr::eq(actual,callable.fn_abi()));callable.validate(graph.module()).unwrap();}
   if name=="source_typed_relay"{let f=&graph.module().functions[0];let sig=graph.module().func_type(f.ty).unwrap();if instance.args.types().any(|t|t.is_unit()){assert_eq!(sig.params[1],trust_ir::Ty::Unit);assert!(sig.returns.is_empty());}else{let trust_ir::Ty::Array(element,3)=sig.params[1]else{panic!("actual shifted namespace")};assert!(element.index()>0);}}
   if instance.args.types().any(|t|t.is_unit()){for callable in graph.callables(){assert!(callable.fn_abi().ret.layout.ty.is_unit());assert!(matches!(callable.fn_abi().ret.mode,rustc_target::callconv::PassMode::Ignore));let f=graph.module().function_by_id(callable.function()).unwrap();assert!(graph.module().func_type(f.ty).unwrap().returns.is_empty());}}
   assert!(graph.module().functions.iter().all(|f|f.body_gate==Some(trust_ir::BodyGate::Ungated)));
   rows.push(serde_json::json!({"name":name,"actual_external_owner":true,"source_nodes":source.visited_expressions(),"complete_original_slots":source.bindings().slots.len(),"source_bound_bodies":records.len(),"actual_fnabi_records":graph.callables().len(),"actual_args":format!("{args:?}"),"new_canonical_compiler_or_rmeta":false,"source_refinement_or_admission":false}));
  }
  assert_eq!(rows.len(),15);assert_eq!(refusals.len(),0);println!("{}",serde_json::to_string_pretty(&serde_json::json!({"upstream_source_graphs":rows,"upstream_source_refusals":refusals,"production_MIR_capture_added":false})).unwrap());
  rustc_driver::Compilation::Continue
 }
}
fn main(){let mut a:Vec<_>=std::env::args().collect();a.push("-Zno-steal-thir".into());rustc_driver::run_compiler(&a,&mut Probe);}
