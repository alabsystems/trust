#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
extern crate serde_json;
extern crate trust_ir;
extern crate trust_ir_build;
extern crate trust_thir_lower as producer;
use producer::rmeta_entry as entry;
use producer::template_metadata as meta;
use rustc_middle::ty;
use serde_json::json;
use std::path::PathBuf;
// Deliberately bypass the writer to model a party able to recompute the public
// content digest. The actual producer module/owner/map remain unchanged.
fn reseal_evidence(good: &[u8], bindings: &meta::OwnerBindings, evidence: &[u8]) -> Vec<u8> {
    let slots: usize = bindings
        .slots
        .iter()
        .map(|s| match s.kind {
            meta::SlotKind::Lifetime => 17,
            meta::SlotKind::Type(_) => 21,
            meta::SlotKind::Const { .. } => 22,
        })
        .sum();
    let payload = &good[56..];
    let module_len_at = 21 + slots + 32;
    let n = u64::from_le_bytes(
        payload[module_len_at..module_len_at + 8]
            .try_into()
            .unwrap(),
    ) as usize;
    let mut changed = payload[..module_len_at + 8 + n].to_vec();
    changed.extend_from_slice(&(evidence.len() as u64).to_le_bytes());
    changed.extend_from_slice(evidence);
    let mut preimage = good[..16].to_vec();
    preimage.extend_from_slice(&changed);
    let digest =
        trust_ir::proof::ProofDigest::sha256_domain("trust.rmeta.template-envelope.v1", &preimage);
    let mut out = good[..16].to_vec();
    out.extend_from_slice(&digest.bytes);
    out.extend_from_slice(&(changed.len() as u64).to_le_bytes());
    out.extend_from_slice(&changed);
    out
}
struct Reader;
impl rustc_driver::Callbacks for Reader {
    fn after_analysis<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: ty::TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        let out = PathBuf::from(std::env::var_os("OFFICIAL_READER_OUT").unwrap());
        std::fs::create_dir_all(&out).unwrap();
        let mut rows = vec![];
        for def in tcx.hir_body_owners() {
            let caller =
                rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(def.to_def_id()));
            let Ok((thir, _)) = tcx.thir_body(def) else {
                continue;
            };
            let thir = thir.borrow();
            for e in &thir.exprs {
                let rustc_middle::thir::ExprKind::Call { fun, .. } = e.kind else {
                    continue;
                };
                let ty::FnDef(item, args) = *thir.exprs[fun].ty.kind() else {
                    continue;
                };
                if item.is_local()
                    || tcx.crate_name(item.krate).as_str() != "official_template_fixture"
                {
                    continue;
                }
                let expected = meta::rustc::owner_bindings(tcx, item).unwrap();
                let header = tcx
                    .trust_ir_crate_header(item.krate)
                    .expect("actual producer header");
                assert!(header.crate_refusal.is_none());
                assert_eq!(header.entry_schema, entry::ENTRY_SCHEMA);
                assert_eq!(header.trust_ir_version, trust_ir::binary::VERSION);
                let mut row = json!({"caller":caller,"definition":tcx.def_path_str(item),"owner":expected.owner,"independent_Rust_slots":format!("{:?}",expected.slots),"proof_authority":false});
                let Some(blob) = tcx.trust_ir_entry(item) else {
                    row["producer_refusal"] = json!(
                        header
                            .unencoded_reason(item.index.as_u32())
                            .expect("every missing expected row is disclosed")
                    );
                    rows.push(row);
                    continue;
                };
                std::fs::write(
                    out.join(format!("{}.entry", caller.replace("::", "_"))),
                    &blob.0,
                )
                .unwrap();
                if !tcx.generics_of(item).requires_monomorphization(tcx) {
                    let r =
                        entry::decode_entry_for_overflow(&blob.0, tcx.sess.overflow_checks())
                            .expect("real R metadata binds its producer overflow mode");
                    assert_eq!(
                        (r.binding.stable_crate_id, r.binding.local_hash),
                        expected.owner
                    );
                    assert!(meta::read(&blob.0, &expected, tcx.sess.overflow_checks()).is_err());
                    row["kind"] = json!("R");
                    row["R_digest"] = json!(r.digest);
                    rows.push(row);
                    continue;
                }
                let a = match meta::rustc::load_upstream(tcx, item) {
                    Ok(a) => a,
                    Err(e) => {
                        row["S_read_refusal"] = json!(e.0);
                        rows.push(row);
                        continue;
                    }
                };
                assert!(entry::decode_entry(&blob.0).is_err());
                assert!(trust_ir_build::template::validate_template(a.template()).is_empty());
                let ev = entry::encode_evidence(a.evidence());
                assert_eq!(
                    meta::frame(&expected, a.template(), a.overflow_checks(), &ev).unwrap(),
                    blob.0
                );
                row["kind"] = json!("S");
                row["content_digest"] = json!(a.digest());
                row["template_digest"] = json!(a.template().digest().unwrap().bytes);
                row["retained_evidence"] = json!(format!("{:?}", a.evidence()));
                row["template"] = json!(format!("{:?}", a.template()));
                let mut wrong = expected.clone();
                wrong.owner.1 ^= 1;
                let resealed = meta::frame(&wrong, a.template(), a.overflow_checks(), &ev).unwrap();
                assert!(
                    meta::read(&resealed, &expected, tcx.sess.overflow_checks())
                        .unwrap_err()
                        .0
                        .contains("owner mismatch")
                );
                let mut wrong = expected.clone();
                wrong
                    .slots
                    .iter_mut()
                    .find(|s| !matches!(s.kind, meta::SlotKind::Lifetime))
                    .unwrap()
                    .definition
                    .1 ^= 1;
                let resealed = meta::frame(&wrong, a.template(), a.overflow_checks(), &ev).unwrap();
                assert!(
                    meta::read(&resealed, &expected, tcx.sess.overflow_checks())
                        .unwrap_err()
                        .0
                        .contains("positional binding")
                );
                assert!(
                    meta::read(&blob.0, &expected, !tcx.sess.overflow_checks())
                        .unwrap_err()
                        .0
                        .contains("overflow-check mode")
                );
                for at in [8, 12, blob.0.len() - 1] {
                    let mut bad = blob.0.clone();
                    bad[at] ^= 1;
                    assert!(meta::read(&bad, &expected, tcx.sess.overflow_checks()).is_err());
                }
                row["real_owner_slot_digest_schema_overflow_tampering_refused"] = json!(true);
                let mut bad = a.evidence().clone();
                bad.arg_count += 1;
                bad.arg_enum.push(false);
                let bad = entry::encode_evidence(&bad);
                assert!(meta::frame(&expected, a.template(), a.overflow_checks(), &bad).is_err());
                let forged = reseal_evidence(&blob.0, &expected, &bad);
                let arity = meta::read(&forged, &expected, tcx.sess.overflow_checks()).unwrap_err();
                assert!(arity.0.contains("argument"), "{arity}");
                let mut bad = a.evidence().clone();
                bad.ledger.push(entry::EvidenceLedgerRow {
                    func_id: u32::MAX,
                    ids: vec![expected.owner],
                    site: None,
                });
                let bad = entry::encode_evidence(&bad);
                assert!(meta::frame(&expected, a.template(), a.overflow_checks(), &bad).is_err());
                let forged = reseal_evidence(&blob.0, &expected, &bad);
                let ledger =
                    meta::read(&forged, &expected, tcx.sess.overflow_checks()).unwrap_err();
                assert!(
                    ledger.0.contains("extra or duplicate declaration"),
                    "{ledger}"
                );
                row["recomputed_actual_evidence_arity_ledger_tampering_refused"] = json!(true);

                let instance = ty::Instance::try_resolve(
                    tcx,
                    ty::TypingEnv::fully_monomorphized(),
                    item,
                    args.skip_binder(),
                )
                .unwrap()
                .unwrap();
                if caller.contains("apply_") {
                    let refusal = meta::instantiate::construct(tcx, instance)
                        .err()
                        .expect("callable body/capture/borrow adapter is not implemented");
                    assert!(refusal.0.contains("unsupported callable/nominal/borrow"));
                    row["runtime_adapter_refusal"] = json!(refusal.0);
                    rows.push(row);
                    continue;
                }
                let graph = match meta::instantiate::construct(tcx, instance) {
                    Ok(g) => g,
                    Err(e) => {
                        row["construct_refusal"] = json!(e.0);
                        rows.push(row);
                        continue;
                    }
                };
                let m = graph.module();
                assert!(trust_ir_build::validate::validate_module(m).is_empty());
                assert!(m.functions.iter().all(
                    |f| !f.is_declaration() && f.body_gate == Some(trust_ir::BodyGate::Ungated)
                ));
                let relay = caller.contains("relay") || caller.contains("slots");
                assert_eq!(m.functions.len(), if relay { 2 } else { 1 });
                use trust_ir::interpret::{
                    InterpretInt, InterpretValue as V, InterpretValueKind as K, Interpreter,
                };
                let cases = if caller.contains("const") {
                    vec![0]
                } else {
                    vec![0, 1, 255, 0x12345678, u64::MAX as i128]
                };
                let mut executions = vec![];
                for sample in cases {
                    let ft = &m.func_types[m.functions[0].ty.as_usize()];
                    let input: Vec<V> = ft
                        .params
                        .iter()
                        .map(|ty| V {
                            ty: ty.clone(),
                            kind: K::Int(InterpretInt {
                                bits: 64,
                                signed: false,
                                raw: sample as u128,
                            }),
                        })
                        .collect();
                    let expected = if caller.contains("const") {
                        u64::MAX as u128
                    } else {
                        sample as u128
                    };
                    let result = Interpreter::with_module(m)
                        .execute_func(graph.entry(), input)
                        .unwrap();
                    assert_eq!(
                        result.returns,
                        vec![V {
                            ty: trust_ir::Ty::U64,
                            kind: K::Int(InterpretInt {
                                bits: 64,
                                signed: false,
                                raw: expected
                            })
                        }]
                    );
                    assert_eq!(result.host_calls, 0);
                    executions.push(json!({"sample":sample,"returns":format!("{:?}",result.returns),"host_calls":result.host_calls}));
                }
                row["functions"] = json!(m.functions.len());
                row["module"] = json!(m);
                row["executions"] = json!(executions);
                rows.push(row);
            }
        }
        std::fs::write(
            out.join("ALL.json"),
            serde_json::to_vec_pretty(&rows).unwrap(),
        )
        .unwrap();
        assert_eq!(rows.len(), 12);
        for name in [
            "use_identity",
            "use_relay",
            "use_slots",
            "use_scalar_const",
            "use_const_relay",
            "use_apply_once",
            "use_apply_ref",
            "use_apply_mut",
        ] {
            let r = rows.iter().find(|r| r["caller"] == name).unwrap();
            assert_eq!(r["kind"], "S", "{r}");
        }
        for name in [
            "use_identity",
            "use_relay",
            "use_slots",
            "use_scalar_const",
            "use_const_relay",
        ] {
            let r = rows.iter().find(|r| r["caller"] == name).unwrap();
            assert!(
                r["executions"].is_array(),
                "real body construction/execution required: {r}"
            );
        }
        for name in ["use_apply_once", "use_apply_ref", "use_apply_mut"] {
            let r = rows.iter().find(|r| r["caller"] == name).unwrap();
            assert!(
                r["runtime_adapter_refusal"].is_string(),
                "no callable admission: {r}"
            );
        }
        for name in ["use_mix", "use_twice"] {
            let r = rows.iter().find(|r| r["caller"] == name).unwrap();
            assert_eq!(r["kind"], "R");
        }
        assert_eq!(
            rows.iter()
                .filter_map(|r| r["executions"].as_array())
                .map(Vec::len)
                .sum::<usize>(),
            17
        );
        for (name, reason) in [
            ("use_tracked", "caller-location"),
            ("use_overflow", "unsited-panic"),
        ] {
            let r = rows.iter().find(|r| r["caller"] == name).unwrap();
            assert!(r["producer_refusal"].as_str().unwrap().starts_with(reason));
        }
        rustc_driver::Compilation::Continue
    }
}
fn main() {
    let mut args: Vec<_> = std::env::args().collect();
    args.extend([
        "-Zno-steal-thir".into(),
        "--sysroot".into(),
        std::env::var("OFFICIAL_READER_SYSROOT").unwrap(),
    ]);
    rustc_driver::run_compiler(&args, &mut Reader);
}
