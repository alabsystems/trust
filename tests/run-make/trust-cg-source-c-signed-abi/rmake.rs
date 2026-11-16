//! Genuine source FnAbi + signed full-W0 Compiler output. Auxiliary metadata
//! remains separately disclosed. A matching source compiler must execute this.
//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64
//@ ignore-cross-compile
use run_make_support::{cc,cmd,rfs,rustc,rustc_path,serde_json};
use std::collections::BTreeSet;
fn abi<'a>(stderr:&'a str,name:&str)->&'a str {
 let head=format!("error: fn_abi_of({name})");let start=stderr.find(&head).unwrap();let rest=&stderr[start+head.len()..];
 let end=rest.find("error: fn_abi_of(").map_or(stderr.len(),|i|start+head.len()+i);&stderr[start..end]
}
fn main(){
 let observed=rustc().input("abi_probe.rs").edition("2024").arg("-Cpanic=abort").arg("-Ztrust-verify=off").run_fail().stderr_utf8();
 for(name,extension)in[("c_i8","Sext"),("c_i16","Sext"),("rust_i8","None"),("rust_i16","None"),("c_u32","None")]{
  let row=abi(&observed,name).split_whitespace().collect::<String>();assert_eq!(row.matches("mode:Direct(").count(),2,"{name}: {row}");assert_eq!(row.matches(&format!("arg_ext:{extension}")).count(),2,"{name}: {row}");
 }
 for opt in["0","3"]{
  let object=format!("native-{opt}.o");let args=["subject.rs","--edition=2024","--crate-type=lib","--crate-name=source_c_signed","--emit=obj","-Cpanic=abort","-Ccodegen-units=1","-Coverflow-checks=off","-Zunstable-options","-Ztrust-verify=off","-Ztrust-ir-lower=on","-Ztrust-ir-flip=no","-Zcodegen-backend=trust-cg","-Ztrust-cg-frontend=trust-ir","-Ztrust-cg-f1-backend=compiler"];
  cmd(rustc_path()).args(args).arg(format!("-Copt-level={opt}")).arg("-o").arg(&object).run();
  let report:serde_json::Value=serde_json::from_str(&rfs::read_to_string(format!("native-{opt}.trust-cg-certificates.json"))).unwrap();
  let expected:BTreeSet<_>=[8,16].into_iter().flat_map(|w|["id","not","tail","store"].into_iter().map(move|n|format!("trust_c_i{w}_{n}"))).collect();
  let rows=report["certificates"].as_array().unwrap();let actual:BTreeSet<_>=rows.iter().map(|r|r["symbol"].as_str().unwrap().to_owned()).collect();
  assert_eq!(rows.len(),8,"{report}");assert_eq!(actual,expected,"{report}");
  let closed:BTreeSet<_>=report["closure"]["closed_kernel"].as_array().unwrap().iter().map(|s|s.as_str().unwrap().to_owned()).collect();assert_eq!(closed,expected,"{report}");assert!(report["closure"]["unclosed"].as_array().unwrap().is_empty(),"{report}");
  for row in rows{
   let symbol=row["symbol"].as_str().unwrap();let width=if symbol.contains("i16"){16}else{8};
   assert_eq!(row["grade"],"[PROVED]","{row}");
   let contract=&row["abi_contracts"][symbol];assert_eq!(contract["schema"],format!("trust-cg-bridge.darwin-c-i{width}-extension.v1"),"{row}");
   assert_eq!(contract["placement_sha256"],row["placement_sha256"][symbol],"{row}");
   for slot in contract["slots"].as_array().unwrap(){assert_eq!(slot["declared_width"],width);assert_eq!(slot["required_width"],32);assert_eq!(slot["extension"],"Sext");}
   if symbol.ends_with("_store"){assert!(row["original_proof"].is_object(),"{row}");}
   if symbol.ends_with("_tail")&&opt=="3"{let sites=row["call_sites"].as_array().unwrap();assert_eq!(sites.len(),1,"{row}");assert_eq!(sites[0]["kind"],"Tail","{row}");}
  }
  // Function Strict and all8 rows are qualified separately from unwind metadata.
  let driver=format!("driver-{opt}");cc().arg("-O2").arg("-Wall").arg("-Wextra").arg("-Werror").input("driver.c").input("observe.S").input(&object).out_exe(&driver).run();cmd(format!("./{driver}")).run();
 }
}
