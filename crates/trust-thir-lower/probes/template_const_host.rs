//! Actual Rustc metadata/CTFE/layout host-primitive controls. No official S
//! producer, runtime admission, sealed body token, codegen or proof claim.
#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
extern crate serde_json;
extern crate trust_ir;
extern crate trust_thir_lower;
use rustc_middle::ty::{self,TyCtxt};
use rustc_span::def_id::{DefId,CRATE_DEF_INDEX};
use trust_thir_lower::template_key::{self,HoleKey,KeyConstItem,KeyArg,KeyTy};
use trust_ir::{Constant,Ty};
fn stable(tcx:TyCtxt<'_>,def:DefId)->(u64,u64){let h=tcx.def_path_hash(def);(h.stable_crate_id().as_u64(),h.local_hash().as_u64())}
fn named(tcx:TyCtxt<'_>,name:&str)->DefId{
 let mut found:Vec<_>=tcx.hir_crate_items(()).definitions().map(|d|d.to_def_id()).filter(|&d|tcx.opt_item_name(d).is_some_and(|n|n.as_str()==name)).collect();
 if found.is_empty(){for &krate in tcx.crates(()){if tcx.crate_name(krate).as_str()=="template_const_host_source"{let root=DefId{krate,index:CRATE_DEF_INDEX};found.extend(tcx.module_children(root).iter().filter(|c|c.ident.name.as_str()==name).filter_map(|c|c.res.opt_def_id()));}}}
 assert_eq!(found.len(),1,"actual named source definition {name}");found[0]
}
fn refusal(result:Result<Constant,trust_thir_lower::template_metadata::MetadataError>,expected:&str)->String{let error=result.expect_err("hostile host input must refuse").0;assert_eq!(error,expected);error}
struct Probe;
impl rustc_driver::Callbacks for Probe{
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->rustc_driver::Compilation{
  let trait_def=named(tcx,"Values");let layout=named(tcx,"Layout");let owner=named(tcx,"owner");
  let main=named(tcx,"main").as_local().unwrap();let(thir,_)=tcx.thir_body(main).unwrap();let thir=thir.borrow();let mut instances=Vec::new();
  for expr in &thir.exprs{if let rustc_middle::thir::ExprKind::Call{fun,..}=expr.kind{
   if let ty::FnDef(def,args)=*thir.exprs[fun].ty.kind(){if def==owner{assert!(args.bound_vars().is_empty());let args=tcx.erase_and_anonymize_regions(args.skip_binder());assert_eq!(args.len(),3,"full lifetime/type/const positions");instances.push(ty::Instance::try_resolve(tcx,ty::TypingEnv::fully_monomorphized(),def,args).unwrap().unwrap());}}
  }}drop(thir);assert_eq!(instances.len(),2);
  let mut rows=Vec::new();
  for instance in instances{
   let small=matches!(instance.args[1].as_type().unwrap().kind(),ty::Uint(ty::UintTy::U8));
   for(name,kind,wanted)in[("SIGNED",Ty::I8,Constant::Int(if small{-7}else{42})),("FLAG",Ty::Bool,Constant::Bool(small)),("WIDE",Ty::U128,Constant::u128(if small{u128::MAX}else{7})),("FLOAT",Ty::F32,Constant::Float(if small{-0.0}else{1.5}))]{
    let item=tcx.associated_items(trait_def).in_definition_order().find(|item|tcx.item_name(item.def_id).as_str()==name).unwrap().def_id;
    let key=template_key::encode(&HoleKey::Const(KeyConstItem::Assoc{item:stable(tcx,item),args:vec![KeyArg::Type(KeyTy::Param(1))]})).unwrap();
    let value=trust_thir_lower::template_metadata::const_host::resolve(tcx,instance,&key,&kind).unwrap();
    match (&value,&wanted) {
     (Constant::Float(actual),Constant::Float(expected))=>assert_eq!(actual.to_bits(),expected.to_bits(),"exact selected floating value {name}"),
     _=>assert_eq!(value,wanted,"actual selected trait impl {name}"),
    }
    let mut refusals=vec![refusal(trust_thir_lower::template_metadata::const_host::resolve(tcx,instance,&key,&Ty::U64),"template associated constant actual Rust type differs from requested IR type")];
    if name=="SIGNED"{refusals.push(refusal(trust_thir_lower::template_metadata::const_host::resolve(tcx,instance,&key,&Ty::U8),"template associated constant actual Rust type differs from requested IR type"));}
    if name=="FLOAT"{refusals.push(refusal(trust_thir_lower::template_metadata::const_host::resolve(tcx,instance,&key,&Ty::U32),"template associated constant actual Rust type differs from requested IR type"));}
    rows.push(serde_json::json!({"case":name,"actual_type":format!("{}",instance.args[1].as_type().unwrap()),"value":format!("{value:?}"),"semantic_match":true,"refusals":refusals,"owner_is_local":instance.def_id().is_local(),"official_S_admission":false}));
   }
   let key=template_key::encode(&HoleKey::Const(KeyConstItem::FieldOffset{adt:Box::new(KeyTy::Adt(stable(tcx,layout),vec![KeyArg::Type(KeyTy::Param(1))])),variant:0,field:1})).unwrap();
   let value=trust_thir_lower::template_metadata::const_host::resolve(tcx,instance,&key,&Ty::Usize).unwrap();
   let oracle=named(tcx,if small{"EXPECT_U8"}else{"EXPECT_U16"});let bits=tcx.const_eval_poly(oracle).unwrap().try_to_scalar_int().unwrap();
   let wanted=Constant::u128(bits.to_bits(tcx.data_layout.pointer_size()));assert_eq!(value,wanted,"Rustc source offset_of oracle");
   let mut refusals=vec![refusal(trust_thir_lower::template_metadata::const_host::resolve(tcx,instance,&key,&Ty::U64),"template field offset must have the target usize type")];
   for(variant,field,param)in[(1,1,1),(0,99,1),(0,1,0),(0,1,2)]{
    let bad=template_key::encode(&HoleKey::Const(KeyConstItem::FieldOffset{adt:Box::new(KeyTy::Adt(stable(tcx,layout),vec![KeyArg::Type(KeyTy::Param(param))])),variant,field})).unwrap();
    let expected=if variant!=0{"template enum/union payload offsets require their qualified layout transport"}else if field==99{"template field offset names an absent declared field"}else{"template key parameter is not a type"};
    refusals.push(refusal(trust_thir_lower::template_metadata::const_host::resolve(tcx,instance,&bad,&Ty::Usize),expected));
   }
   let mut malformed_args=instance.args.iter().collect::<Vec<_>>();malformed_args[1]=tcx.lifetimes.re_erased.into();
   let malformed=ty::Instance{def:instance.def,args:tcx.mk_args(&malformed_args)};
   refusals.push(refusal(trust_thir_lower::template_metadata::const_host::resolve(tcx,malformed,&key,&Ty::Usize),"template key generic argument kind"));
   let bad=template_key::encode(&HoleKey::Const(KeyConstItem::Assoc{item:stable(tcx,owner),args:vec![]})).unwrap();
   refusals.push(refusal(trust_thir_lower::template_metadata::const_host::resolve(tcx,instance,&bad,&Ty::U64),"template constant key definition is not an associated constant"));
   rows.push(serde_json::json!({"case":"FIELD_OFFSET","actual_type":format!("{}",instance.args[1].as_type().unwrap()),"value":format!("{value:?}"),"semantic_match":true,"refusals":refusals,"owner_is_local":instance.def_id().is_local(),"official_S_admission":false}));
  }
  assert_eq!(rows.len(),10);println!("{}",serde_json::to_string_pretty(&rows).unwrap());rustc_driver::Compilation::Continue
 }
}
fn main(){let mut args:Vec<_>=std::env::args().collect();args.push("-Zno-steal-thir".into());rustc_driver::run_compiler(&args,&mut Probe);}
