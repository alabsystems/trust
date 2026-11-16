//! Actual-source ABI extraction observer. Built against the changed compiler's rustc crates.
//! This checks emitted source conventions and refusals, not physical ABI or proof grades.
#![feature(rustc_private)]
extern crate rustc_abi;
extern crate rustc_driver;
extern crate rustc_data_structures;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
extern crate rustc_target;
extern crate serde_json;
extern crate trust_ir;
extern crate trust_thir_lower;
use rustc_abi::ExternAbi;
use rustc_target::spec::Arch;
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LocalDefId;
use trust_ir::{CallingConv, Inst};
use trust_thir_lower::calling_convention::{AbiSource, FunctionAbi};

fn named(tcx: TyCtxt<'_>, name: &str) -> LocalDefId {
    let found: Vec<_> = tcx.hir_crate_items(()).definitions().filter(|&d|
        tcx.opt_item_name(d.to_def_id()).is_some_and(|n| n.as_str() == name)).collect();
    assert_eq!(found.len(), 1, "actual source identity {name}");
    found[0]
}
fn lowered<'tcx>(tcx: TyCtxt<'tcx>, name: &str) -> trust_thir_lower::Lowered {
    let owner = named(tcx, name);
    let (stored, root) = tcx.thir_body(owner).expect("original source THIR");
    assert!(!stored.is_stolen(), "actual THIR of {name} must be available");
    let thir = stored.borrow();
    trust_thir_lower::lower_module_from_thir_for_query(tcx, owner, &thir, root).0
}
struct Probe;
impl rustc_driver::Callbacks for Probe {
    fn after_analysis<'tcx>(&mut self, _: &rustc_interface::interface::Compiler, tcx: TyCtxt<'tcx>) -> rustc_driver::Compilation {
        let mut bodies = vec![
            ("rust_body", ExternAbi::Rust, CallingConv::Rust),
            ("c_body", ExternAbi::C { unwind: false }, CallingConv::C),
            ("unwind_body", ExternAbi::C { unwind: true }, CallingConv::CUnwind),
            ("system_body", ExternAbi::System { unwind: false }, CallingConv::C),
            ("efi_body", ExternAbi::EfiApi, CallingConv::EfiApi),
            ("cold_body", ExternAbi::RustCold, CallingConv::RustCold),
        ];
        // The subject and observer use the SAME actual host target; other target ABIs are
        // covered by the exact mapper controls, not fabricated rustc owner/target records.
        if tcx.sess.target.is_like_windows && tcx.sess.target.arch == Arch::X86 {
            panic!("this host's system ABI is stdcall and must be tested as an explicit refusal");
        }
        if tcx.sess.target.is_like_darwin { bodies.push(("swift_body", ExternAbi::Swift, CallingConv::Swift)); }
        if tcx.sess.target.arch == Arch::X86_64 {
            bodies.push(("sysv_body", ExternAbi::SysV64 { unwind: false }, CallingConv::SysV64));
            bodies.push(("win_body", ExternAbi::Win64 { unwind: false }, CallingConv::Win64));
            bodies.push(("vector_body", ExternAbi::Vectorcall { unwind: false }, CallingConv::VectorCall));
        }
        if tcx.sess.target.arch == Arch::Arm { bodies.push(("aapcs_body", ExternAbi::Aapcs { unwind: false }, CallingConv::Aapcs)); }
        let mut rows = Vec::new();
        for (name, source, convention) in &bodies {
            let def = named(tcx, name);
            let original = tcx.fn_sig(def).skip_binder().skip_binder();
            assert_eq!(original.abi(), *source);
            let abi = FunctionAbi::of_definition(tcx, def.to_def_id());
            assert_eq!(abi.source(), AbiSource::Declared { abi: *source, c_variadic: false });
            assert_eq!(abi.calling_conv(), Ok(*convention));
            let out = lowered(tcx, name);
            assert!(out.unsupported.is_empty(), "{name}: {:?}", out.unsupported);
            assert_eq!(out.module.functions[0].calling_conv, *convention);
            rows.push(serde_json::json!({"case":name,"source_abi":source.as_str(),"emitted":format!("{convention:?}"),"fully_lowered":true,"module_digest":out.module.stable_digest().to_string(),"module_debug":format!("{:?}",out.module),"callee_ledger_debug":format!("{:?}",out.callees)}));
        }
        for (name, source, convention) in [
            ("direct_c", ExternAbi::C { unwind: false }, CallingConv::C),
            ("direct_unwind", ExternAbi::C { unwind: true }, CallingConv::CUnwind),
            ("direct_system", ExternAbi::System { unwind: false }, CallingConv::C),
        ] {
            let out = lowered(tcx, name);
            assert!(out.unsupported.is_empty(), "{name}: {:?}", out.unsupported);
            assert_eq!(out.callees.len(), 1);
            if name == "direct_c" {
                let variadic = named(tcx, "foreign_variadic");
                assert!(tcx.fn_sig(variadic).skip_binder().skip_binder().c_variadic());
                assert_eq!(FunctionAbi::of_definition(tcx, variadic.to_def_id()).source(),
                    AbiSource::Declared { abi: ExternAbi::C { unwind: false }, c_variadic: true });
            }
            assert_eq!(out.callees[0].abi.source(), AbiSource::Declared { abi: source, c_variadic: false });
            assert_eq!(out.callees[0].abi.calling_conv(), Ok(convention));
            assert_eq!(out.module.functions[0].calling_conv, CallingConv::Rust);
            rows.push(serde_json::json!({"case":name,"source_abi":source.as_str(),"callee_ledger":format!("{convention:?}"),"fully_lowered":true,"module_digest":out.module.stable_digest().to_string(),"module_debug":format!("{:?}",out.module),"callee_ledger_debug":format!("{:?}",out.callees)}));
        }
        // This exact original-source call must decline before its signed bodyless
        // RustCold aggregate declaration can invalidate the assembled whole module.
        let out = lowered(tcx, "direct_cold_layout");
        assert!(out.unsupported.iter().any(|(_, reason)|
            *reason == "Callee(foreign-ABI repr(Rust) struct by value)"),
            "call-specific layout refusal: {:?}", out.unsupported);
        assert_eq!(out.callees.len(), 1);
        assert_eq!(out.callees[0].abi.source(),
            AbiSource::Declared { abi: ExternAbi::RustCold, c_variadic: false });
        assert_eq!(out.callees[0].abi.calling_conv(), Ok(CallingConv::RustCold));
        assert!(out.callees[0].abi.is_rust_convention(), "unsigned-signature policy stays Rust");
        assert!(out.callees[0].abi.needs_foreign_layout_check(), "separate exact IR layout policy");
        rows.push(serde_json::json!({"case":"direct_cold_layout","refused":true,
            "reasons":format!("{:?}",out.unsupported),"module_digest":out.module.stable_digest().to_string(),
            "module_debug":format!("{:?}",out.module),"callee_ledger_debug":format!("{:?}",out.callees)}));
        for (name, convention) in [
            ("indirect_rust", CallingConv::Rust), ("indirect_c", CallingConv::C),
        ] {
            let out = lowered(tcx, name);
            assert!(out.unsupported.is_empty(), "{name}: {:?}", out.unsupported);
            let calls: Vec<_> = out.module.functions[0].blocks.iter().flat_map(|b| &b.body).filter_map(|n|
                if let Inst::CallIndirect { calling_conv, .. } = &n.inst { Some(*calling_conv) } else { None }).collect();
            assert_eq!(calls, vec![convention], "exact original call population {name}");
            rows.push(serde_json::json!({"case":name,"indirect_edges":1,"emitted":format!("{convention:?}"),"module_digest":out.module.stable_digest().to_string(),"module_debug":format!("{:?}",out.module)}));
        }
        for name in ["tuple_protocol", "indirect_tuple", "indirect_unwind", "indirect_system", "indirect_cold"] {
            let out = lowered(tcx, name);
            let required = if name == "tuple_protocol" {
                assert!(FunctionAbi::of_definition(tcx, named(tcx, name).to_def_id()).calling_conv().is_err());
                "BodyHeader(unsupported source ABI or missing body)"
            } else { "Call(fn-ptr unsupported ABI)" };
            assert!(out.unsupported.iter().any(|(_, reason)| *reason == required), "{name}: {:?}", out.unsupported);
            if name.starts_with("indirect_") {
                assert!(!out.module.functions.iter().flat_map(|f| &f.blocks).flat_map(|b| &b.body)
                    .any(|n| matches!(n.inst, Inst::CallIndirect { .. })), "no relabeled indirect edge");
            }
            rows.push(serde_json::json!({"case":name,"refused":true,"reasons":format!("{:?}",out.unsupported),"module_digest":out.module.stable_digest().to_string(),"module_debug":format!("{:?}",out.module),"callee_ledger_debug":format!("{:?}",out.callees)}));
        }
        let out = lowered(tcx, "closure_adapter");
        assert!(out.fnptr_adapter, "actual compiler-owned adapter remains disclosed/refused by splice");
        assert!(out.module.functions.len() > 1);
        assert!(out.module.functions.iter().all(|f| f.calling_conv == CallingConv::Rust));
        rows.push(serde_json::json!({"case":"closure_adapter","explicit_adapted_rust":true,"splice_admitted":false,"module_digest":out.module.stable_digest().to_string(),"module_debug":format!("{:?}",out.module),"callee_ledger_debug":format!("{:?}",out.callees)}));
        let expected = bodies.len() + 3 + 1 + 2 + 5 + 1;
        assert_eq!(rows.len(), expected);
        println!("{}", serde_json::to_string_pretty(&serde_json::json!({"status":"PASS_SOURCE_ABI_ONLY","case_count":expected,"rows":rows,"physical_abi_proof":false,"proof_grade_promotion":false})).unwrap());
        rustc_driver::Compilation::Stop
    }
}
fn main() {
    // FIRST native-main operation: capture the actual inherited scheduler before
    // arguments, descriptor-opening work or threads. No context is cleared or minted.
    if let Err(error) = unsafe { rustc_data_structures::jobserver::capture_early() } {
        eprintln!("embedded compiler early custody refused: {error}");
        std::process::exit(75);
    }
    let mut args: Vec<String> = std::env::args().collect();
    args[0] = "rustc".into();
    args.push("-Zno-steal-thir".into());
    rustc_driver::run_compiler(&args, &mut Probe);
}
