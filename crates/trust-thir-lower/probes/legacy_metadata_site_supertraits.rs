#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
extern crate serde_json;
extern crate trust_thir_lower as producer;
use producer::metadata_site as site;
use rustc_middle::ty::{self, TypeVisitableExt};
use serde_json::json;
fn bytes(hex:&str)->Vec<u8>{hex.as_bytes().chunks_exact(2).map(|p|u8::from_str_radix(std::str::from_utf8(p).unwrap(),16).unwrap()).collect()}
fn hex(bytes:&[u8])->String{bytes.iter().map(|b|format!("{b:02x}")).collect()}
struct Observer;
impl rustc_driver::Callbacks for Observer {
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:ty::TyCtxt<'tcx>)->rustc_driver::Compilation{
  let out=std::path::PathBuf::from(std::env::var_os("SITE_READER_OUT").unwrap());std::fs::create_dir_all(&out).unwrap();let mut rows=Vec::new();
  for def in tcx.hir_body_owners(){
   let caller=rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(def.to_def_id()));
   let Ok((thir,_))=tcx.thir_body(def)else{continue};let thir=thir.borrow();
   for e in &thir.exprs{
    let rustc_middle::thir::ExprKind::Call{fun,..}=e.kind else{continue};
    let ty::FnDef(item,args)=*thir.exprs[fun].ty.kind()else{continue};
    if item.is_local()||tcx.crate_name(item.krate).as_str()!="legacy_site_fixture"{continue}
    let env=ty::TypingEnv::fully_monomorphized();let args=tcx.try_normalize_erasing_regions(env,ty::EarlyBinder::bind(tcx,args.skip_binder()).instantiate_identity()).unwrap();assert!(!args.has_non_region_param()&&!args.has_infer());
    let actual=ty::Instance::try_resolve(tcx,env,item,args).unwrap().unwrap();let key=site::canonical_suffix(tcx,actual).unwrap();let recovered=site::recover(tcx,&key).unwrap();assert_eq!(recovered.instance(),actual);assert_eq!(site::canonical_suffix(tcx,recovered.instance()).unwrap(),key);
    let raw=bytes(&key);assert_eq!(raw.len(),205);assert_eq!(&raw[134..137],b"u16");assert_eq!(raw[166],if caller=="case_super4"{4}else{5});
    let mut bad_const=raw.clone();bad_const[166]=3;let const_error=site::recover(tcx,&hex(&bad_const)).err().expect("supertrait const substitution mismatch refuses").to_string();
    let mut bad_type=raw.clone();bad_type[125]=3;bad_type[134]=b'i';let type_error=site::recover(tcx,&hex(&bad_type)).err().expect("supertrait type substitution mismatch refuses").to_string();
    std::fs::write(out.join(format!("{caller}.key")),&key).unwrap();rows.push(json!({"caller":caller,"canonical":key,"actual_instance":format!("{actual:?}"),"site_args":format!("{:?}",recovered.site_args()),"exact_instance_and_canonical_match":true,"wrong_supertrait_const":const_error,"wrong_supertrait_type":type_error,"proof_authority":false}));
   }
  }
  std::fs::write(out.join("ALL.json"),serde_json::to_vec_pretty(&rows).unwrap()).unwrap();assert_eq!(rows.len(),2);assert_ne!(rows[0]["canonical"],rows[1]["canonical"]);let expected:Vec<String>=serde_json::from_slice(&std::fs::read(std::env::var_os("SITE_READER_EXPECTED").unwrap()).unwrap()).unwrap();assert_eq!(rows.iter().map(|r|r["caller"].as_str().unwrap().to_string()).collect::<std::collections::BTreeSet<_>>(),expected.into_iter().collect());rustc_driver::Compilation::Continue
 }
}
fn main(){let mut args:Vec<_>=std::env::args().collect();args.extend(["-Zno-steal-thir".into(),"--sysroot".into(),std::env::var("SITE_READER_SYSROOT").unwrap()]);rustc_driver::run_compiler(&args,&mut Observer)}
