//! Real upstream crate-store observations only. No source-TV/admission claim.
#![feature(rustc_private)]
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
extern crate serde_json;
extern crate trust_ir;
extern crate trust_ir_build;
extern crate trust_thir_lower;
use rustc_middle::ty::{self, TyCtxt};
use serde_json::json;
use std::collections::BTreeMap;
use trust_thir_lower::{
    rmeta_entry as entry,
    source_word64::{self as source, record},
};

fn owner(tcx: TyCtxt<'_>, def: rustc_span::def_id::DefId) -> record::Definition {
    let hash = tcx.def_path_hash(def);
    record::Definition {
        stable_crate_id: hash.stable_crate_id().as_u64(),
        local_hash: hash.local_hash().as_u64(),
    }
}
fn reseal(bytes: &mut [u8]) {
    let length = (16 + bytes.len() - 56) as u64;
    let mut digest =
        trust_ir::proof::ProofDigest::sha256_domain_stream("trust.rmeta.entry-envelope.v1", length);
    digest.update(&bytes[..16]).unwrap();
    digest.update(&bytes[56..]).unwrap();
    bytes[16..48].copy_from_slice(&digest.finish().unwrap().bytes);
}
// Retain the actual core implementation and its original-source claim together.
// This is data intake for independent mathematics, never Rust-source TV.
fn retain_core_callee(tcx: TyCtxt<'_>, out: &std::path::Path, definition: record::Definition) {
    let callee = trust_thir_lower::template_key::rustc::definition(tcx,
        (definition.stable_crate_id, definition.local_hash)).unwrap();
    assert_eq!(tcx.crate_name(callee.krate).as_str(), "core");
    let header = tcx.trust_ir_crate_header(callee.krate).unwrap();
    assert_eq!(header.entry_schema, 6);
    assert!(header.crate_refusal.is_none());
    let blob = tcx.trust_ir_entry(callee).expect("actual core callee implementation");
    // Retain the producer's real mode. Data decoding grants no mode-mismatch admission.
    let decoded = entry::decode_entry(&blob.0).unwrap();
    assert_eq!(owner(tcx, callee), definition);
    assert_eq!((decoded.binding.stable_crate_id, decoded.binding.local_hash),
               (definition.stable_crate_id, definition.local_hash));
    let source = decoded.source.as_ref().expect("actual core source claim required");
    assert_eq!(source.owner, definition);
    assert_eq!(source.parameters.len(), 2);
    let record::Body::Call { definition: intrinsic, kind: source::CallKind::RegisteredWrappingAdd,
                            generic_u64: true, operands, .. } = &source.body
        else { panic!("core source is not the registered intrinsic: {source:?}") };
    assert_eq!(operands.iter().map(|(_, value)| value.clone()).collect::<Vec<_>>(),
               [source::Operand::Parameter(0), source::Operand::Parameter(1)]);
    let intrinsic = trust_thir_lower::template_key::rustc::definition(tcx,
        (intrinsic.stable_crate_id, intrinsic.local_hash)).unwrap();
    assert_eq!(intrinsic.krate, callee.krate);
    let registration = tcx.intrinsic(intrinsic).expect("actual compiler registration");
    assert!(registration.must_be_overridden);
    assert_eq!(registration.name.as_str(), "wrapping_add");
    assert!(trust_ir_build::validate_module(&decoded.module).is_empty());
    assert_eq!(decoded.module.functions.len(), 1);
    let function = &decoded.module.functions[0];
    assert!(!function.is_declaration());
    let signature = decoded.module.func_type(function.ty).unwrap();
    assert_eq!(signature.params, [trust_ir::Ty::U64, trust_ir::Ty::U64]);
    assert_eq!(signature.returns, [trust_ir::Ty::U64]);
    let evidence = entry::decode_evidence(&decoded.evidence).unwrap();
    assert!(trust_thir_lower::effect_conservation::retained::judge(
        &decoded.module, &evidence).unwrap().tags().is_empty());
    let module = trust_ir::binary::serialize_module(&decoded.module).unwrap();
    let record = record::encode(source).unwrap();
    let report = serde_json::to_vec_pretty(&json!({
        "owner": format!("{definition:?}"), "source_hash": source.source_hash,
        "producer_overflow_checks": decoded.overflow_checks,
        "consumer_overflow_checks": tcx.sess.overflow_checks(),
        "source_kind": "RegisteredWrappingAdd", "parameters": 2,
        "actual_registration_rechecked": true, "actual_D28_rechecked": true,
        "proof_authority": false, "scope": "Original source claim and unchanged IR data only"
    })).unwrap();
    for (name, bytes) in [("core-callee.entry", blob.0.as_slice()),
                          ("core-callee.module", module.as_slice()),
                          ("core-callee.source", record.as_slice()),
                          ("CORE-CALLEE.json", report.as_slice())] {
        let path = out.join(name);
        if path.exists() { assert_eq!(std::fs::read(path).unwrap(), bytes); }
        else { std::fs::write(path, bytes).unwrap(); }
    }
}
struct Observer;
impl rustc_driver::Callbacks for Observer {
    fn after_analysis<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        assert_eq!(entry::ENTRY_SCHEMA, 6, "matching rebuilt SDK required");
        let out = std::path::PathBuf::from(std::env::var_os("SOURCE_ENTRY_OUT").unwrap());
        std::fs::create_dir(&out).unwrap();
        let mut rows = BTreeMap::new();
        for local in tcx.hir_body_owners() {
            let (thir, _) = tcx.thir_body(local).unwrap();
            let thir = thir.borrow();
            for expression in &thir.exprs {
                let rustc_middle::thir::ExprKind::Call { fun, .. } = expression.kind else {
                    continue;
                };
                let ty::FnDef(def, _) = *thir.exprs[fun].ty.kind() else {
                    continue;
                };
                if def.is_local() || tcx.crate_name(def.krate).as_str() != "source_claim_dep" {
                    continue;
                }
                let name = tcx.item_name(def).to_string();
                assert!(["identity", "double", "pair", "statements", "located"].contains(&name.as_str()));
                let header = tcx
                    .trust_ir_crate_header(def.krate)
                    .expect("actual producer header");
                assert_eq!(header.entry_schema, 6);
                assert!(header.crate_refusal.is_none());
                if name == "located" {
                    assert!(tcx.trust_ir_entry(def).is_none(), "legacy caller-location refusal lost");
                    let reason = header.unencoded_reason(def.index.as_u32())
                        .expect("legacy inventory needs its named producer refusal");
                    assert!(reason.starts_with("caller-location("), "{reason}");
                    assert!(rows.insert(name, json!({"source_present": null,
                        "producer_refusal": reason, "actual_D28_rechecked": false,
                        "proof_authority": false})).is_none());
                    continue;
                }
                let blob = tcx.trust_ir_entry(def).unwrap_or_else(|| panic!(
                    "actual producer entry is mandatory for {name}: {:?}",
                    header.unencoded_reason(def.index.as_u32())
                ));
                let decoded =
                    entry::decode_entry_for_overflow(&blob.0, tcx.sess.overflow_checks()).unwrap();
                let actual = owner(tcx, def);
                assert_eq!(
                    (decoded.binding.stable_crate_id, decoded.binding.local_hash),
                    (actual.stable_crate_id, actual.local_hash)
                );
                assert_eq!(
                    trust_ir::binary::deserialize_module(
                        &trust_ir::binary::serialize_module(&decoded.module).unwrap()
                    )
                    .unwrap(),
                    decoded.module
                );
                let evidence = entry::decode_evidence(&decoded.evidence).unwrap();
                let judgement = trust_thir_lower::effect_conservation::retained::judge(
                    &decoded.module,
                    &evidence,
                )
                .unwrap();
                assert!(
                    judgement.tags().is_empty(),
                    "source data cannot replace D28"
                );
                if name == "statements" {
                    assert!(
                        decoded.source.is_none(),
                        "unsupported source silently acquired a model"
                    );
                } else {
                    let source = decoded
                        .source
                        .as_ref()
                        .expect("main producer must retain original source");
                    assert_eq!(source.owner, actual);
                    let location = tcx
                        .sess
                        .source_map()
                        .lookup_char_pos(tcx.def_span(def).lo());
                    assert_eq!(source.source_hash, location.file.src_hash.to_string());
                    assert_eq!(source.parameters.len(), if name == "pair" { 2 } else { 1 });
                    match (&*name, &source.body) {
                        (
                            "identity",
                            record::Body::Operand {
                                value: source::Operand::Parameter(0),
                                ..
                            },
                        ) => {}
                        (
                            "double" | "pair",
                            record::Body::Call {
                                kind: source::CallKind::OrdinaryCall,
                                definition,
                                operands,
                                ..
                            },
                        ) => {
                            assert!(evidence.ledger.iter().any(|row| row.ids.contains(&(
                                definition.stable_crate_id, definition.local_hash,
                            ))), "original source call target must agree with the actual D28 ledger");
                            retain_core_callee(tcx, &out, *definition);
                            assert_eq!(operands[0].1, source::Operand::Parameter(0));
                            assert_eq!(
                                operands[1].1,
                                source::Operand::Parameter(if name == "pair" { 1 } else { 0 })
                            );
                        }
                        _ => panic!("actual original source operation was lost: {source:?}"),
                    }
                    // Keep all real envelope/module/evidence bytes intact except
                    // the source owner, then recompute the digest. Owner checks
                    // must refuse independently of digest integrity.
                    let mut wrong = source.clone();
                    wrong.owner.local_hash ^= 1;
                    let wire = record::encode(&wrong).unwrap();
                    let mut bytes = blob.0.clone();
                    let start = bytes.len() - wire.len();
                    bytes[start..].copy_from_slice(&wire);
                    reseal(&mut bytes);
                    assert!(matches!(
                        entry::decode_entry(&bytes),
                        Err(entry::EntryDecodeError::Source(_))
                    ));
                    std::fs::write(out.join(format!("{name}.wrong-owner.entry")), bytes).unwrap();
                    let mut bytes = blob.0.clone();
                    *bytes.last_mut().unwrap() ^= 1;
                    assert_eq!(
                        entry::decode_entry(&bytes).unwrap_err(),
                        entry::EntryDecodeError::EnvelopeDigest
                    );
                }
                std::fs::write(out.join(format!("{name}.entry")), &blob.0).unwrap();
                assert!(rows.insert(name, json!({"source_present": decoded.source.is_some(),
                    "source_claim": format!("{:?}", decoded.source), "original_module_digest": decoded.digest,
                    "actual_D28_rechecked": true, "proof_authority": false})).is_none());
            }
        }
        assert_eq!(rows.len(), 5, "all four non-inline controls and the legacy refusal are mandatory");
        std::fs::write(
            out.join("RESULTS.json"),
            serde_json::to_vec_pretty(&rows).unwrap(),
        )
        .unwrap();
        rustc_driver::Compilation::Stop
    }
}
fn main() {
    // First main operation: capture actual inherited scheduler descriptors.
    if let Err(error) = unsafe { rustc_data_structures::jobserver::capture_early() } {
        eprintln!("early custody refused: {error}");
        std::process::exit(75);
    }
    let mut args: Vec<_> = std::env::args().collect();
    args.push("-Zno-steal-thir".into());
    rustc_driver::run_compiler(&args, &mut Observer);
}
