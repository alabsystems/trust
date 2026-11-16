//! Offline evidence harness. A kernel check under a stored context does NOT
//! bind that context to a program. Missing original VC bytes remain a refusal.

use std::fs;
use std::io::Read;
use std::path::Path;

use serde_json::{Value, json};
use trust_types::{JsonProofReport, ObligationReport, SourceSpan, VcKind};

use super::*;

mod capture;
mod panic_aggregate;

fn hash(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn bound_read(path: &Path, expected: &str, limit: u64) -> Result<Vec<u8>, String> {
    bound_read_with_hooks(path, expected, limit, || {}, || {})
}

// The hooks exercise replacement/growth at the actual opened-file boundaries.
// This entire module is test-only; the audit uses the no-hook wrapper above.
fn bound_read_with_hooks(
    path: &Path,
    expected: &str,
    limit: u64,
    after_stat: impl FnOnce(),
    after_open: impl FnOnce(),
) -> Result<Vec<u8>, String> {
    let before = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !before.is_file() || before.file_type().is_symlink() || before.len() > limit {
        return Err("input must be a bounded regular file".into());
    }
    after_stat();
    // Preserve the retired Python reader's Unix open behavior: a leaf swapped
    // to a symlink is not followed, and a FIFO cannot block before fstat.
    #[cfg(unix)]
    let file = fs::File::from(
        nix::fcntl::open(
            path,
            nix::fcntl::OFlag::O_RDONLY
                | nix::fcntl::OFlag::O_CLOEXEC
                | nix::fcntl::OFlag::O_NOFOLLOW
                | nix::fcntl::OFlag::O_NONBLOCK,
            nix::sys::stat::Mode::empty(),
        )
        .map_err(|error| format!("input open refused: {error}"))?,
    );
    #[cfg(not(unix))]
    let file = fs::File::open(path).map_err(|e| e.to_string())?;
    let opened = file.metadata().map_err(|e| e.to_string())?;
    if !opened.is_file() {
        return Err("opened input is not a regular file".into());
    }
    if !same_file(&before, &opened) {
        return Err("input identity changed before opening".into());
    }
    after_open();
    let mut reader = file.take(limit.saturating_add(1));
    let mut bytes = Vec::new();
    reader.read_to_end(&mut bytes).map_err(|e| e.to_string())?;
    let opened_after = reader.get_ref().metadata().map_err(|e| e.to_string())?;
    let after = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !after.is_file()
        || after.file_type().is_symlink()
        || !same_file(&before, &after)
        || !same_file(&before, &opened_after)
        || bytes.len() as u64 != before.len()
        || bytes.len() as u64 > limit
        || before.len() != after.len()
        || before.modified().ok() != after.modified().ok()
        || hash(&bytes) != expected
    {
        return Err("input source/report SHA256 or metadata mismatch".into());
    }
    Ok(bytes)
}

fn same_file(left: &fs::Metadata, right: &fs::Metadata) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        left.dev() == right.dev()
            && left.ino() == right.ino()
            && left.mode() == right.mode()
            && left.len() == right.len()
            && left.mtime() == right.mtime()
            && left.mtime_nsec() == right.mtime_nsec()
            && left.ctime() == right.ctime()
            && left.ctime_nsec() == right.ctime_nsec()
    }
    #[cfg(not(unix))]
    {
        left.len() == right.len() && left.modified().ok() == right.modified().ok()
    }
}

/// Reuse the real decoder, fresh environment, kernel check and axiom-closure
/// audit. Unknown constants are diagnostic Int skolems, NEVER program facts.
fn stored_context_check(term: &[u8], context: &[u8]) -> bool {
    on_certify_stack(|| {
        let term_expr = deserialize_term(term).ok()?;
        let reduced: ReducedContext = deserialize_context(context).ok()?;
        let mut names = Vec::new();
        if !collect_const_names(&term_expr, &mut names) {
            return Some(false);
        }
        for decl in &reduced.decls {
            if !collect_const_names(&decl.type_, &mut names)
                || decl.value.as_ref().is_some_and(|v| !collect_const_names(v, &mut names))
            {
                return Some(false);
            }
        }
        let base = base_env()?;
        let mut vars = BTreeSet::new();
        for name in names {
            if base.get_const(&name).is_some() {
                continue;
            }
            let name = name.to_string();
            let raw = if let Some(encoded) = name.strip_prefix("trust_var_") {
                if encoded.len() % 2 != 0 || !encoded.bytes().all(|b| b.is_ascii_hexdigit()) {
                    return Some(false);
                }
                let bytes = (0..encoded.len())
                    .step_by(2)
                    .map(|i| u8::from_str_radix(&encoded[i..i + 2], 16))
                    .collect::<Result<Vec<_>, _>>()
                    .ok()?;
                String::from_utf8(bytes).ok()?
            } else {
                name.clone()
            };
            if encoded_var_name(&raw) != name {
                return Some(false);
            }
            vars.insert(raw);
        }
        Some(payload_roundtrip_rechecks(&vars, term, context))
    })
    .unwrap_or(false)
}

fn native_binding(
    native: &trust_types::TransportNativeTrustIrEvidence,
    public_id: &str,
) -> Result<Value, String> {
    if !trust_types::native_trust_ir_artifact_shape_is_publishable(native) {
        return Err("native structural digest/request/proof envelope refused".into());
    }
    let mut payloads = BTreeMap::new();
    for artifact in &native.artifacts {
        let bytes = artifact.materialization.as_ref().unwrap().decoded_bytes()?;
        let envelope: Value = serde_json::from_slice(&bytes).map_err(|e| e.to_string())?;
        let role = envelope["role"].as_str().ok_or("missing native role")?.to_string();
        if payloads.insert(role, envelope["payload"].clone()).is_some() {
            return Err("duplicate native role".into());
        }
    }
    let bundle: trust_ir::NativeVerificationBundle =
        serde_json::from_value(payloads["bundle"].clone()).map_err(|e| e.to_string())?;
    bundle.validate().map_err(|e| format!("typed bundle refused: {e:?}"))?;
    let request: trust_ir::NativeVerificationRequest =
        serde_json::from_value(payloads["request"].clone()).map_err(|e| e.to_string())?;
    let request_json = serde_json::to_value(&request).map_err(|e| e.to_string())?;
    let matching = bundle
        .requests
        .iter()
        .filter(|candidate| serde_json::to_value(candidate).ok().as_ref() == Some(&request_json))
        .count();
    if matching != 1 {
        return Err("request is not an exact unique member of the typed bundle".into());
    }
    let proof_id = payloads["normalized_obligation"].as_u64().ok_or("bad proof id")?;
    let request_body =
        request_json.as_object().and_then(|o| o.values().next()).ok_or("bad request")?;
    if request_body["id"].as_u64().map(|n| n.to_string()) != native.request_id
        || !request_body["obligations"].as_array().is_some_and(|ids| ids.contains(&json!(proof_id)))
    {
        return Err("selected proof is not bound to the selected request".into());
    }
    let selected: Vec<_> = bundle
        .module
        .proof_obligations
        .iter()
        .filter_map(|o| serde_json::to_value(o).ok())
        .filter(|o| o["id"].as_u64() == Some(proof_id))
        .collect();
    if selected.len() != 1 || selected[0]["source"]["public"]["obligation_id"] != public_id {
        return Err("native public obligation identity mismatch".into());
    }
    Ok(json!({"request_id": native.request_id, "proof_id": proof_id,
        "native_source_digest": bundle.provenance.source_digest,
        "native_formula_schema": selected[0]["formula"]["schema"],
        "native_binding": "typed_structural_only_not_original_vc_or_source_extraction"}))
}

fn qualification_controls() {
    let x = || Formula::Var("replay_control_x".into(), Sort::Int);
    let vc = VerificationCondition {
        kind: VcKind::Assertion { message: "offline replay qualification".into() },
        function: "replay_control::original".into(),
        location: SourceSpan::default(),
        formula: Formula::And(vec![
            Formula::Lt(Box::new(x()), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(Formula::Int(0)), Box::new(x())),
        ]),
        contract_metadata: None,
        obligation: None,
    };
    let evidence = certify_vc(&vc).expect("explicit control VC, never a report replacement");
    let trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } = &evidence else {
        panic!()
    };
    assert!(replay_vc_evidence(&vc, &evidence), "identity-aware consumer control");
    assert!(stored_context_check(term, context), "actual stored bytes kernel control");
    let bad_term = serialize_term(&Expr::const_(Name::from_string("True.intro"), vec![])).unwrap();
    assert!(!stored_context_check(&bad_term, context), "wrong term cannot inhabit False");
    assert!(!stored_context_check(term, &[]), "truncated context must refuse");
    let mut changed = evidence.clone();
    if let trust_ir::ProofEvidence::CleanCic { term, .. } = &mut changed {
        *term = bad_term;
    }
    assert!(!replay_vc_evidence(&vc, &changed), "consumer must refuse altered stored term");
    let mut changed = evidence.clone();
    if let trust_ir::ProofEvidence::CleanCic { context, .. } = &mut changed {
        context.clear();
    }
    assert!(!replay_vc_evidence(&vc, &changed), "consumer must refuse altered stored context");
    for field in ["goal", "source", "request"] {
        let mut changed = vc.clone();
        match field {
            "goal" => changed.formula = Formula::Bool(true),
            "source" => changed.location.file = "other-source.rs".into(),
            "request" => changed.function = "replay_control::other_request".into(),
            _ => unreachable!(),
        }
        assert!(!replay_vc_evidence(&changed, &evidence), "{field} identity must refuse");
        assert_ne!(
            lineage_digest(term, context, &ObligationIdentity::from_vc(&changed).unwrap()),
            *lineage
        );
    }
}

#[test]
fn stored_payload_qualification_controls() {
    qualification_controls();
}

#[test]
fn original_vc_snapshot_direct_presented_check_and_adversarial_controls() {
    let x = || Formula::Var("snapshot_x".into(), Sort::Int);
    let vc = VerificationCondition {
        function: "original::snapshot_fixture".into(),
        kind: VcKind::Assertion { message: "original full claim".into() },
        location: SourceSpan { file: "original.rs".into(), ..SourceSpan::default() },
        formula: Formula::And(vec![
            Formula::Lt(Box::new(x()), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(Formula::Int(0)), Box::new(x())),
        ]),
        contract_metadata: None,
        obligation: None,
    };
    let evidence = certify_vc(&vc).expect("control producer only, not a report replay");
    let target = "aarch64-apple-darwin;ptr64";
    let id = "vc:original::snapshot_fixture:assert:0";
    let capture = |vc: &VerificationCondition| {
        let digest =
            trust_types::original_vc_snapshot::exact_vc_claim_digest_sha256(vc, true, Some(target))
                .unwrap();
        trust_types::OriginalVcSnapshot::capture(vc, true, target, id, &digest).unwrap()
    };
    let snapshot = capture(&vc);
    assert!(recheck_presented_linear_int_vc(&vc, &evidence));
    assert!(recheck_presented_original_vc_snapshot(&snapshot, &vc, id, true, target, &evidence));
    assert!(!recheck_presented_original_vc_snapshot(
        &snapshot,
        &vc,
        "wrong-request-row",
        true,
        target,
        &evidence
    ));
    assert!(!recheck_presented_original_vc_snapshot(&snapshot, &vc, id, false, target, &evidence));
    assert!(!recheck_presented_original_vc_snapshot(
        &snapshot,
        &vc,
        id,
        true,
        "other-target",
        &evidence
    ));

    let relineage = |vc: &VerificationCondition, term: Vec<u8>, context: Vec<u8>| {
        let identity = ObligationIdentity::from_vc(vc).unwrap();
        trust_ir::ProofEvidence::CleanCic {
            lineage: lineage_digest(&term, &context, &identity),
            term,
            context,
            kernel_recheck: None,
        }
    };
    let trust_ir::ProofEvidence::CleanCic { term, context, .. } = &evidence else { panic!() };
    // Recompute the public lineage on each tamper: failure must not rely only
    // on a stale checksum. The actual presented term cannot prove False.
    let wrong_term =
        serialize_term(&Expr::const_(Name::from_string("True.intro"), vec![])).unwrap();
    assert!(!recheck_presented_linear_int_vc(&vc, &relineage(&vc, wrong_term, context.clone())));
    assert!(!recheck_presented_linear_int_vc(
        &vc,
        &relineage(&vc, term.clone(), canonical_empty_context_bytes().unwrap())
    ));
    let oracle = serialize_term(&Expr::const_(Name::from_string("sorry"), vec![])).unwrap();
    assert!(!recheck_presented_linear_int_vc(&vc, &relineage(&vc, oracle, context.clone())));

    // A supplied False hypothesis trivially checks under its SELF-ASSERTED
    // context; it must not match the context reconstructed from this VC.
    let forged_id = FVarId::new(HYP_FVAR_BASE);
    let mut forged = LocalContext::new();
    forged.push_with_id(
        forged_id,
        Name::from_string("h_0"),
        Expr::const_(Name::from_string("False"), vec![]),
        BinderInfo::Default,
    );
    let forged_context = serialize_context(&reduced_context(&forged)).unwrap();
    let forged_term = serialize_term(&Expr::fvar(forged_id)).unwrap();
    assert!(stored_context_check(&forged_term, &forged_context));
    assert!(!recheck_presented_linear_int_vc(&vc, &relineage(&vc, forged_term, forged_context)));

    for dimension in ["function", "source", "goal", "metadata"] {
        let mut wrong = vc.clone();
        match dimension {
            "function" => wrong.function = "foreign::function".into(),
            "source" => wrong.location.file = "foreign.rs".into(),
            "goal" => wrong.formula = Formula::Lt(Box::new(x()), Box::new(Formula::Int(0))),
            _ => {
                wrong.contract_metadata =
                    Some(trust_types::ContractMetadata { has_requires: true, ..Default::default() })
            }
        }
        assert!(
            !recheck_presented_original_vc_snapshot(&snapshot, &wrong, id, true, target, &evidence),
            "{dimension}"
        );
        let self_asserted = capture(&wrong);
        let forged_lineage = relineage(&wrong, term.clone(), context.clone());
        assert!(
            !recheck_presented_original_vc_snapshot(
                &self_asserted,
                &vc,
                id,
                true,
                target,
                &forged_lineage
            ),
            "independent expected {dimension}"
        );
        if dimension == "goal" {
            assert!(
                !recheck_presented_linear_int_vc(&wrong, &forged_lineage),
                "SAT goal cannot borrow old context"
            );
        }
    }
    std::thread::scope(|scope| {
        scope
            .spawn(|| {
                let mut deep = vc.clone();
                let mut ty = trust_types::Ty::u64();
                for _ in 0..10_000 {
                    ty = trust_types::Ty::Ref { mutable: false, inner: Box::new(ty) };
                }
                deep.kind = VcKind::NegationOverflow { ty };
                assert!(!recheck_presented_linear_int_vc(&deep, &evidence));
                assert!(!recheck_presented_original_vc_snapshot(
                    &snapshot, &deep, id, true, target, &evidence
                ));
                std::mem::forget(deep); // refuse before recursive serialization/Drop
            })
            .join()
            .unwrap();
    });
    println!(
        "original VC snapshot: direct presented kernel check PASS; row/semantics/term/context/oracle/source/goal/metadata controls PASS; source program authority NOT established"
    );
}

#[test]
#[ignore = "requires an explicit results capture/digest and owned fresh output path"]
fn audit_saved_native_reports() {
    let capture_path =
        std::env::var_os("TRUST_NATIVE_REPLAY_RESULTS").expect("explicit results capture");
    let capture_path = Path::new(&capture_path);
    let capture_hash =
        std::env::var("TRUST_NATIVE_REPLAY_RESULTS_SHA256").expect("explicit results SHA256");
    let output = std::env::var_os("TRUST_NATIVE_REPLAY_OUTPUT").expect("owned fresh output");
    let output = Path::new(&output);
    capture::require_fresh_output(output).unwrap();
    let cases = capture::read_capture(capture_path, &capture_hash).unwrap();
    qualification_controls();
    let mut results = Vec::new();
    for case in &cases {
        let path = &case.report;
        let raw = bound_read(path, &case.report_sha256, capture::REPORT_LIMIT).unwrap();
        let source_path = &case.source;
        let source_hash = &case.source_sha256;
        bound_read(source_path, source_hash, capture::SOURCE_LIMIT).unwrap();
        assert!(
            bound_read(source_path, &"0".repeat(64), 1024 * 1024).is_err(),
            "wrong source snapshot must refuse"
        );
        let (saved, sanitization, _) = JsonProofReport::decode_saved_json(&raw, None).unwrap();
        assert_eq!(saved.summary.total_proved, 0, "saved claims grant no authority");
        let wire: Value = serde_json::from_slice(&raw).unwrap();
        let mut rows = Vec::new();
        for function in wire["functions"].as_array().unwrap() {
            for row in function["obligations"].as_array().unwrap() {
                let typed: ObligationReport = serde_json::from_value(row.clone()).unwrap();
                assert!(
                    typed
                        .transport_evidence
                        .as_ref()
                        .and_then(|t| t.original_vc_snapshot.as_ref())
                        .is_none(),
                    "historical reports do not contain an original full VC: keep exact-program replay refused"
                );
                let structural_defect =
                    trust_types::saved_obligation_structural_proof_defect(&typed, None);
                let mut result = json!({"obligation_id": row["obligation_id"], "function": function["function"],
                    "reported_status": row["outcome"]["status"], "reported_backend": row["proof_evidence"]["backend"],
                    "reported_strength": row["outcome"]["strength"], "reported_proof_id": row["proof_evidence"]["proof_id"],
                    "claim_digest_sha256": row["transport_evidence"]["claim_digest_sha256"],
                    "typed_kind": row["transport_evidence"]["typed_kind"],
                    "reported_source_identity": row["transport_evidence"]["identity"],
                    "exact_program_replay": false, "exact_claim_binding": "not_attempted_no_stored_clean_cic",
                    "structural_defect": structural_defect});
                if let Some(native) =
                    typed.transport_evidence.as_ref().and_then(|t| t.native_trust_ir.as_ref())
                {
                    let id = typed.obligation_id.as_deref().unwrap_or("");
                    let binding = native_binding(native, id);
                    if binding.is_ok() {
                        let mut wrong = native.clone();
                        wrong.request_id = Some("4294967295".into());
                        assert!(
                            native_binding(&wrong, id).is_err(),
                            "wrong native request must refuse"
                        );
                        assert!(
                            native_binding(native, "wrong-public-goal").is_err(),
                            "wrong public goal must refuse"
                        );
                        result["native_negative_controls"] =
                            "request_and_public_goal_rejected_after_positive_binding".into();
                    }
                    result["native_binding"] = json!(binding);
                }
                if let Some(proof) = typed.proof_evidence.as_ref() {
                    let artifacts: Vec<_> =
                        proof.artifacts.iter().filter(|a| a.kind == "clean_cic").collect();
                    if !artifacts.is_empty() {
                        assert_eq!(artifacts.len(), 1);
                        let evidence: trust_ir::ProofEvidence =
                            serde_json::from_value(artifacts[0].metadata.clone().unwrap()).unwrap();
                        let trust_ir::ProofEvidence::CleanCic {
                            term,
                            context,
                            lineage,
                            kernel_recheck,
                        } = evidence
                        else {
                            panic!()
                        };
                        result["stored_term_sha256"] = hash(&term).into();
                        result["stored_context_sha256"] = hash(&context).into();
                        result["stored_lineage"] = json!(lineage);
                        assert!(
                            kernel_recheck.is_none(),
                            "this audit is scoped to the retained VC payloads"
                        );
                        result["kernel_recheck_directive_present"] =
                            kernel_recheck.is_some().into();
                        result["exact_claim_binding"] =
                            "refused_missing_original_full_vc_payload".into();
                        let checked = stored_context_check(&term, &context);
                        if checked {
                            let replacement = serialize_term(&Expr::const_(
                                Name::from_string("True.intro"),
                                vec![],
                            ))
                            .unwrap();
                            assert!(
                                !stored_context_check(&replacement, &context),
                                "stored term replacement cannot inhabit False"
                            );
                            let truncated = &context[..context.len().checked_sub(1).unwrap()];
                            assert!(
                                !stored_context_check(&term, truncated),
                                "actual stored context truncation must refuse"
                            );
                            result["stored_term_replacement_rejected"] = true.into();
                            result["stored_context_truncation_rejected"] = true.into();
                        }
                        result["unbound_stored_context_kernel_check"] = checked.into();
                    }
                }
                rows.push(result);
            }
        }
        assert_eq!(rows.len(), case.rows);
        bound_read(path, &case.report_sha256, capture::REPORT_LIMIT).unwrap();
        bound_read(source_path, source_hash, capture::SOURCE_LIMIT).unwrap();
        results.push(json!({"case": case.name, "rows": rows, "report_sha256":case.report_sha256, "source_sha256":source_hash,
            "saved_proved_downgraded": sanitization.downgraded_proved,
            "saved_structural_defects": sanitization.structural_evidence_defects}));
    }
    bound_read(capture_path, &capture_hash, capture::CAPTURE_LIMIT).unwrap();
    let receipt = json!({"schema":"trust.native-report-stored-payload-audit.v2",
        "results":capture_path, "results_sha256":capture_hash, "qualification_controls":"pass",
        "boundary":"unbound_stored_context_kernel_checks_are_not_program_proofs",
        "cases":results});
    capture::write_fresh_output(output, &serde_json::to_vec_pretty(&receipt).unwrap()).unwrap();
    println!("stored-payload audit written to {}", output.display());
}
