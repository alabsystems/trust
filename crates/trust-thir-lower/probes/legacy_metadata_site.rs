#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
extern crate serde_json;
extern crate trust_thir_lower as producer;
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use producer::metadata_site as site;
use serde_json::json;
use std::path::PathBuf;
fn bytes(hex: &str) -> Vec<u8> {hex.as_bytes().chunks_exact(2).map(|p|u8::from_str_radix(std::str::from_utf8(p).unwrap(),16).unwrap()).collect()}
fn hex(bytes: &[u8]) -> String {bytes.iter().map(|b|format!("{b:02x}")).collect()}
fn refuse(tcx: TyCtxt<'_>, bytes: &[u8]) -> String {site::recover(tcx,&hex(bytes)).err().expect("hostile site must refuse").to_string()}
fn hash(tcx: TyCtxt<'_>, def: rustc_span::def_id::DefId)->(u64,u64){let h=tcx.def_path_hash(def);(h.stable_crate_id().as_u64(),h.local_hash().as_u64())}
struct Observer;
impl rustc_driver::Callbacks for Observer {
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->rustc_driver::Compilation{
  let out=PathBuf::from(std::env::var_os("SITE_READER_OUT").unwrap());std::fs::create_dir_all(&out).unwrap();let mut rows=Vec::new();
  for def in tcx.hir_body_owners(){
   let caller=rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(def.to_def_id()));
   let Ok((thir,_))=tcx.thir_body(def)else{continue};let thir=thir.borrow();
   for expr in &thir.exprs{
    let rustc_middle::thir::ExprKind::Call{fun,..}=expr.kind else{continue};
    let ty::FnDef(item,args)=*thir.exprs[fun].ty.kind()else{continue};
    if item.is_local()||tcx.crate_name(item.krate).as_str()!="legacy_site_fixture"{continue}
    let env=ty::TypingEnv::fully_monomorphized();
    let args=tcx.try_normalize_erasing_regions(env,ty::EarlyBinder::bind(tcx,args.skip_binder()).instantiate_identity()).expect("actual source args normalize");
    assert!(!args.has_non_region_param()&&!args.has_infer());
    let instance=ty::Instance::try_resolve(tcx,env,item,args).unwrap().expect("actual source Item resolves");
    let key=site::canonical_suffix(tcx,instance).expect("full actual legacy vocabulary must encode");
    let recovered=site::recover(tcx,&key).expect("actual canonical source site recovers");
    assert_eq!(recovered.instance(),instance);assert_eq!(site::canonical_suffix(tcx,recovered.instance()).unwrap(),key);
    let signature=format!("{:?}",tcx.fn_sig(item).instantiate(tcx,args).skip_normalization());
    let mut r=json!({"caller":caller,"definition":tcx.def_path_str(item),"owner":hash(tcx,item),"actual_instance":format!("{instance:?}"),"args":format!("{args:?}"),"site_args":format!("{:?}",recovered.site_args()),"canonical":key,"signature":signature,"exact_instance_and_canonical_match":true,"proof_authority":false});
    let raw=bytes(&key);let mut attacks=serde_json::Map::new();
    for end in 0..key.len(){assert!(site::recover(tcx,&key[..end]).is_err(),"prefix {end}")}
    attacks.insert("all_prefixes".into(),json!(key.len()));
    for(at,value,label)in[(0,2,"version"),(17,255,"instance_kind"),(17,1,"reify_adapter")]{let mut bad=raw.clone();bad[at]=value;attacks.insert(label.into(),json!(refuse(tcx,&bad)));}
    let mut bad=raw.clone();bad.extend_from_slice(&[0]);attacks.insert("trailing".into(),json!(refuse(tcx,&bad)));
    let mut bad=raw.clone();bad[1..9].fill(0);attacks.insert("unloaded_crate".into(),json!(refuse(tcx,&bad)));
    let mut bad=raw.clone();bad[9..17].fill(0);attacks.insert("absent_definition".into(),json!(refuse(tcx,&bad)));
    assert!(site::recover(tcx,&(key.clone()+"G0")).is_err());attacks.insert("noncanonical_hex".into(),json!(true));
    if caller=="case_value_const_1"{
     assert_eq!(raw.len(),64);let mut bad=raw.clone();*bad.last_mut().unwrap()=4;attacks.insert("scalar_type_width".into(),json!(refuse(tcx,&bad)));
     let mut bad=raw.clone();assert_eq!(&bad[36..39],b"u64");bad[27]=3;bad[36]=b'i';attacks.insert("const_declared_type".into(),json!(refuse(tcx,&bad)));
    }
    if caller=="case_value_bool"{let mut bad=raw.clone();assert_eq!(bad.len(),53);bad[44]=2;attacks.insert("invalid_bool".into(),json!(refuse(tcx,&bad)));}
    if caller=="case_value_char"{let mut bad=raw.clone();bad[41..45].copy_from_slice(&0xd800u32.to_be_bytes());attacks.insert("invalid_char".into(),json!(refuse(tcx,&bad)));}
    if caller=="case_value_aggregate"{
     assert_eq!(raw[52],1);assert_eq!(u64::from_be_bytes(raw[53..61].try_into().unwrap()),2);
     let mut bad=raw[..87].to_vec();bad[53..61].copy_from_slice(&1u64.to_be_bytes());attacks.insert("aggregate_field_population".into(),json!(refuse(tcx,&bad)));
     let mut bad=raw.clone();assert_eq!(bad[61],0);assert_eq!(bad[62],0);bad[78]=2;attacks.insert("nested_bool_validity".into(),json!(refuse(tcx,&bad)));
    }
    if caller=="case_value_const_array"{
     let at=raw.windows(3).enumerate().filter(|(_,s)|*s==b"u16").last().unwrap().0;let mut bad=raw.clone();bad[at]=b'i';bad[at-9]=3;attacks.insert("nested_array_child_type".into(),json!(refuse(tcx,&bad)));
    }
    if caller=="case_value_text"{
     let mut needle=vec![4];needle.extend_from_slice(&2u64.to_be_bytes());needle.extend_from_slice(b"u8");needle.push(0);needle.extend_from_slice(&104u128.to_be_bytes());needle.extend_from_slice(&1u64.to_be_bytes());
     let at=raw.windows(needle.len()).position(|s|s==needle).unwrap();let mut bad=raw.clone();bad[at+needle.len()-9]=255;attacks.insert("str_utf8".into(),json!(refuse(tcx,&bad)));
    }
    if caller=="case_nominal"{
     assert_eq!(raw[52],12);let mut bad=raw.clone();bad[52]=0;attacks.insert("positional_erased_region_kind".into(),json!(refuse(tcx,&bad)));
     let mut bad=raw.clone();let(h1,h2)=hash(tcx,item);bad[28..36].copy_from_slice(&h1.to_be_bytes());bad[36..44].copy_from_slice(&h2.to_be_bytes());attacks.insert("nominal_definition_kind".into(),json!(refuse(tcx,&bad)));
    }
    if caller=="case_fn"{
     assert_eq!(raw[27],15);let n=u64::from_be_bytes(raw[28..36].try_into().unwrap())as usize;
     for(delta,label)in[(0,"fn_safety_bool"),(1,"fn_variadic_bool"),(2,"fn_splat_option")]{let mut bad=raw.clone();bad[36+n+delta]=255;attacks.insert(label.into(),json!(refuse(tcx,&bad)));}
    }
    if caller=="case_infer_closure"{let mut bad=raw.clone();assert_eq!(bad[27],16);assert_eq!(bad[28],0);bad[28]=2;attacks.insert("closure_family_owner_mismatch".into(),json!(refuse(tcx,&bad)));let mut bad=raw.clone();let n=bad.len();assert_eq!(bad[n-9],7);assert_eq!(u64::from_be_bytes(bad[n-8..].try_into().unwrap()),0);bad[n-8..].copy_from_slice(&1u64.to_be_bytes());bad.push(0);attacks.insert("closure_capture_metadata_mismatch".into(),json!(refuse(tcx,&bad)));}
    if caller=="case_dyn"{
     assert_eq!(raw.len(),192);assert_eq!(raw[36],0);assert_eq!(raw[99],1);assert_eq!(raw[175],2);
     let bodies=vec![raw[36..99].to_vec(),raw[99..175].to_vec(),raw[175..].to_vec()];
     let mut bad=raw[..36].to_vec();for body in bodies.iter().rev(){bad.extend_from_slice(body)}attacks.insert("dynamic_predicate_order".into(),json!(refuse(tcx,&bad)));
     let mut bad=raw.clone();bad[28..36].copy_from_slice(&4u64.to_be_bytes());bad.extend_from_slice(bodies.last().unwrap());attacks.insert("dynamic_duplicate_predicate".into(),json!(refuse(tcx,&bad)));
     let mut bad=raw[..36].to_vec();bad[28..36].copy_from_slice(&2u64.to_be_bytes());bad.extend_from_slice(&bodies[0]);bad.extend_from_slice(&bodies[2]);attacks.insert("dynamic_missing_projection".into(),json!(refuse(tcx,&bad)));
     let mut bad=raw.clone();assert_eq!(bad[153],4);bad[153]=3;attacks.insert("dynamic_projection_trait_arguments".into(),json!(refuse(tcx,&bad)));
    }
    r["negative_controls"]=json!(attacks);std::fs::write(out.join(format!("{caller}.key")),key).unwrap();rows.push(r);
   }
  }
  std::fs::write(out.join("ALL.json"),serde_json::to_vec_pretty(&rows).unwrap()).unwrap();
  let expected:Vec<String>=serde_json::from_slice(&std::fs::read(std::env::var_os("SITE_READER_EXPECTED").unwrap()).unwrap()).unwrap();
  let actual:std::collections::BTreeSet<_>=rows.iter().map(|r|r["caller"].as_str().unwrap().to_string()).collect();assert_eq!(actual,expected.into_iter().collect());assert_eq!(rows.len(),49);
  for(a,b)in[("case_value_const_1","case_value_const_2"),("case_u64","case_i64")]{let a=rows.iter().find(|r|r["caller"]==a).unwrap();let b=rows.iter().find(|r|r["caller"]==b).unwrap();assert_eq!(a["signature"],b["signature"]);assert_ne!(a["canonical"],b["canonical"]);assert_ne!(a["actual_instance"],b["actual_instance"]);}
  rustc_driver::Compilation::Continue
 }
}
fn main(){let mut args:Vec<_>=std::env::args().collect();args.extend(["-Zno-steal-thir".into(),"--sysroot".into(),std::env::var("SITE_READER_SYSROOT").unwrap()]);rustc_driver::run_compiler(&args,&mut Observer)}
