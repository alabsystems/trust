//! Read-only actual crate-store observer for the schema-6 overflow-mode matrix.
//! Expected invocation modes are assertions only. The consuming mode passed to
//! both decoder routes comes exclusively from the actual Rustc session.
#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_data_structures;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
extern crate serde_json;
extern crate trust_ir;
extern crate trust_thir_lower;

use rustc_middle::ty::{self, TyCtxt};
use serde_json::json;
use trust_thir_lower::rmeta_entry::{self as entry, EntryDecodeError};

fn declared(name: &str) -> bool {
    match std::env::var(name).expect("independent runner invocation record").as_str() {
        "on" => true,
        "off" => false,
        _ => panic!("invalid declared invocation mode"),
    }
}

struct Observer;
impl rustc_driver::Callbacks for Observer {
    fn after_analysis<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        assert_eq!(entry::ENTRY_SCHEMA, 6, "a schema-4 SDK cannot qualify this fixture");
        let actual_consumer = tcx.sess.overflow_checks();
        assert_eq!(actual_consumer, declared("MODE_MATRIX_CONSUMER"));
        let declared_producer = declared("MODE_MATRIX_PRODUCER");
        let out = std::path::PathBuf::from(std::env::var_os("MODE_MATRIX_OUT").unwrap());
        std::fs::create_dir_all(&out).unwrap();
        let mut rows = Vec::new();
        for owner in tcx.hir_body_owners() {
            let (thir, _) = tcx.thir_body(owner).expect("declared fixture body");
            let thir = thir.borrow();
            for expression in &thir.exprs {
                let rustc_middle::thir::ExprKind::Call { fun, .. } = expression.kind else { continue };
                let ty::FnDef(definition, _) = *thir.exprs[fun].ty.kind() else { continue };
                if definition.is_local() || tcx.crate_name(definition.krate).as_str() != "mode_dep" {
                    continue;
                }
                let name = tcx.item_name(definition).to_string();
                assert!(["mix", "identity", "inherited"].contains(&name.as_str()));
                let header = tcx.trust_ir_crate_header(definition.krate)
                    .expect("real canonical producer header is mandatory");
                assert!(header.crate_refusal.is_none());
                assert_eq!(header.entry_schema, 6);
                assert_eq!(header.trust_ir_version, trust_ir::binary::VERSION);
                let (class, column) = entry::upstream_entry_column(tcx, definition);
                if name == "inherited" {
                    assert!(tcx.trust_ir_entry(definition).is_none(),
                        "inherited overflow mode cannot be safely exported");
                    let reason = header.unencoded_reason(definition.index.as_u32())
                        .expect("actual producer must retain its named refusal");
                    assert_eq!(reason, "inherited-overflow-checks(the compiler-only attribute is not exported)");
                    assert_eq!((class, column.as_str()), ("absent", "absent(inherited-overflow-checks)"));
                    rows.push(json!({"definition":name,"consumer_session_mode":actual_consumer,
                        "declared_producer_invocation_mode":declared_producer,"class":class,
                        "column":column,"producer_refusal":reason,"proof_authority":false}));
                    continue;
                }
                let blob = tcx.trust_ir_entry(definition)
                    .expect("a missing/refused producer row cannot count as a mode positive");
                std::fs::write(out.join(format!("{name}.entry")), &blob.0).unwrap();
                let decoded = entry::decode_entry(&blob.0).expect("actual schema-6 producer bytes");
                assert_eq!(decoded.overflow_checks, declared_producer,
                    "compare actual writer field with independent producing invocation, never body inference");
                let hash = tcx.def_path_hash(definition);
                assert_eq!(decoded.binding.stable_crate_id, hash.stable_crate_id().as_u64());
                assert_eq!(decoded.binding.local_hash, hash.local_hash().as_u64());
                assert_eq!(decoded.module.functions.len(), 1);
                let evidence = entry::decode_evidence(&decoded.evidence).expect("retained real evidence");
                assert_eq!(evidence.arg_count, 1);
                // No expected/environment boolean is supplied to this API.
                let checked = entry::decode_entry_for_overflow(&blob.0, actual_consumer);
                if decoded.overflow_checks == actual_consumer {
                    assert_eq!(checked.unwrap().overflow_checks, actual_consumer);
                    assert_eq!(class, "entry");
                    assert!(column.starts_with("entry(digest-ok,functions=1,"));
                } else {
                    assert!(matches!(checked, Err(EntryDecodeError::OverflowMode { producer, consumer })
                        if producer == decoded.overflow_checks && consumer == actual_consumer));
                    assert_eq!(class, "entry-refused");
                    assert_eq!(column, format!(
                        "entry-refused(overflow-check-mode(producer_{},_consumer_{}))",
                        decoded.overflow_checks, actual_consumer));
                }
                rows.push(json!({"definition":name,"producer_retained_mode":decoded.overflow_checks,
                    "declared_producer_invocation_mode":declared_producer,
                    "consumer_session_mode":actual_consumer,"class":class,"column":column,
                    "schema":entry::ENTRY_SCHEMA,"bytes":blob.0.len(),
                    "content_digest":decoded.content_digest,"module_digest":decoded.digest,
                    "proof_authority":false}));
            }
        }
        std::fs::write(out.join("ALL.json"), serde_json::to_vec_pretty(&rows).unwrap()).unwrap();
        assert_eq!(rows.len(), 3, "retain both real R entries and the separate named refusal");
        let names: std::collections::BTreeSet<_> = rows.iter()
            .map(|row| row["definition"].as_str().unwrap()).collect();
        assert_eq!(names, ["mix", "identity", "inherited"].into_iter().collect());
        rustc_driver::Compilation::Continue
    }
}

fn main() {
    // FIRST native-main operation: preserve original SDK/GNU descriptor identity.
    if let Err(error) = unsafe { rustc_data_structures::jobserver::capture_early() } {
        eprintln!("embedded compiler early custody refused: {error}");
        std::process::exit(75);
    }

    let mut args: Vec<_> = std::env::args().collect();
    let expected = std::env::var("MODE_MATRIX_SYSROOT").unwrap();
    let mut supplied = 0;
    for (index, arg) in args.iter().enumerate().skip(1) {
        if arg == "--sysroot" {
            assert_eq!(args.get(index + 1).map(String::as_str), Some(expected.as_str()),
                "observer sysroot differs from the selected canonical SDK");
            supplied += 1;
        } else if let Some(value) = arg.strip_prefix("--sysroot=") {
            assert_eq!(value, expected, "observer sysroot differs from the selected canonical SDK");
            supplied += 1;
        }
    }
    assert!(supplied <= 1, "observer received more than one sysroot");
    if supplied == 0 {
        args.extend(["--sysroot".into(), expected]);
    }
    args.push("-Zno-steal-thir".into());
    rustc_driver::run_compiler(&args, &mut Observer);
}
