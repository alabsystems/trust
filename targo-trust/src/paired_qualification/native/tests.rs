//! Pure census data and actual original pipe controls. No managed SDK,
//! completed candidate, admitted host or proof capability is fabricated.
use std::io::Read as _;

use super::super::ledger::tests::{ledger, records};
use super::*;

#[test]
fn original_stop_pipe_closes_after_bound_stop_and_also_when_no_binding_is_available() {
    for bound in [true, false] {
        let (mut reader, writer) = UnixStream::pair().unwrap();
        reader.set_read_timeout(Some(Duration::from_secs(1))).unwrap();
        let mut writer = Some(writer);
        let binding = service::Binding { root_attempt: [1; 16], invocation_sha256: [2; 32] };
        let result = stop_input(
            &mut writer,
            bound.then_some(&binding),
            1,
            Instant::now() + Duration::from_secs(1),
        );
        assert_eq!(result.is_ok(), bound);
        assert!(writer.is_none());
        if bound {
            let mut size = [0; 4];
            reader.read_exact(&mut size).unwrap();
            let mut frame = vec![0; u32::from_be_bytes(size) as usize];
            reader.read_exact(&mut frame).unwrap();
            assert_eq!(
                service::Control::decode(&frame, &binding, 1).unwrap(),
                service::Control::Stop(binding)
            );
        }
        assert_eq!(
            reader.read(&mut [0; 1]).unwrap(),
            0,
            "actual original EOF must not wait for the outer CLI to exit"
        );
    }
}
#[test]
fn reported_denominator_removal_is_never_a_solver_gain_and_timeout_growth_refuses() {
    let base = ledger(service::Node::Advisory, &records(service::Node::Advisory)).unwrap();
    let mut changed = records(service::Node::Advisory);
    changed[0]["results"].as_array_mut().unwrap().remove(0);
    changed[0]["total"] = json!(2);
    changed[0]["unknown"] = json!(2);
    changed[2]["total_obligations"] = json!(2);
    changed[2]["total_unknown"] = json!(2);
    let current = ledger(service::Node::Advisory, &changed).unwrap();
    let result = ratchet(&base, &current);
    assert_eq!(result["obligations_removed"].as_array().unwrap().len(), 1);
    assert!(result["solver_discharged_identity_gains"].as_array().unwrap().is_empty());
    assert_eq!(result["floors"]["conservative_solver_discharged"], json!([0, 0]));
    let mut changed = records(service::Node::Advisory);
    changed[0]["results"][0]["outcome"] = json!("timeout");
    changed[0]["timed_out"] = json!(2);
    changed[2]["total_timed_out"] = json!(2);
    let current = ledger(service::Node::Advisory, &changed).unwrap();
    assert!(
        ratchet(&base, &current)["ratchet_regressions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|reason| reason == "timeout count rose")
    );
}
#[test]
fn changed_existing_failures_refuse_but_newly_emitted_unknowns_remain_disclosed() {
    let base = ledger(service::Node::Advisory, &records(service::Node::Advisory)).unwrap();
    let mut changed = records(service::Node::Advisory);
    changed[0]["results"][0]["outcome"] = json!("failed");
    changed[0]["failed"] = json!(1);
    changed[0]["unknown"] = json!(2);
    changed[2]["total_failed"] = json!(1);
    changed[2]["total_unknown"] = json!(2);
    let current = ledger(service::Node::Advisory, &changed).unwrap();
    assert!(
        ratchet(&base, &current)["ratchet_regressions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|reason| reason == "failed growth is not explained by newly emitted obligations")
    );
    let mut changed = records(service::Node::Advisory);
    let mut added = changed[0]["results"][0].clone();
    added["kind"] = json!("bounds");
    changed[0]["results"].as_array_mut().unwrap().push(added);
    changed[0]["total"] = json!(4);
    changed[0]["unknown"] = json!(4);
    changed[2]["total_obligations"] = json!(4);
    changed[2]["total_unknown"] = json!(4);
    let current = ledger(service::Node::Advisory, &changed).unwrap();
    let result = ratchet(&base, &current);
    assert_eq!(result["obligations_newly_asked"].as_array().unwrap().len(), 1);
    assert!(result["ratchet_regressions"].as_array().unwrap().is_empty());
    assert!(result["solver_discharged_identity_gains"].as_array().unwrap().is_empty());
}

#[test]
fn replacement_gains_cannot_hide_loss_of_an_existing_discharged_identity() {
    // Pure accounting observations. These edited table values have no live
    // compiler receipt and confer no proof or completed-candidate authority.
    let mut base = ledger(service::Node::Advisory, &records(service::Node::Advisory)).unwrap();
    let mut current = ledger(service::Node::Advisory, &records(service::Node::Advisory)).unwrap();
    let identities = base.entries.keys().cloned().collect::<Vec<_>>();
    let old = base.entries.get_mut(&identities[0]).unwrap();
    old.class = crate::paired_qualification::ledger::Class::ProvedSolver;
    old.conservative_outcome = crate::types::VerificationOutcome::Proved;
    let replacement = current.entries.get_mut(&identities[1]).unwrap();
    replacement.class = crate::paired_qualification::ledger::Class::ProvedSolver;
    replacement.conservative_outcome = crate::types::VerificationOutcome::Proved;
    let result = ratchet(&base, &current);
    assert_eq!(result["floors"]["conservative_solver_discharged"], json!([1, 1]));
    assert_eq!(result["solver_discharged_identity_gains"], json!([identities[1]]));
    assert_eq!(result["solver_discharged_identity_losses"], json!([identities[0]]));
    assert!(
        result["ratchet_regressions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|reason| reason == "existing solver-discharged identities lost proof")
    );
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn original_input_marker_refuses_old_revision_and_retains_new_input_without_delivery() {
    use std::os::unix::fs::PermissionsExt as _;
    // Native file/profile consistency only. These small parser fixtures are
    // NEVER executed, enrolled as SDKs, or represented as completed candidates.
    let base = std::env::current_exe().unwrap().parent().unwrap().canonicalize().unwrap();
    let temporary = tempfile::tempdir_in(base).unwrap();
    let root = temporary.path().join("sdk");
    std::fs::create_dir(&root).unwrap();
    std::fs::create_dir(root.join("bin")).unwrap();
    std::fs::create_dir(root.join("lib")).unwrap();
    let program = root.join("bin/targo");
    let mut image = vec![0u8; 320];
    let put = |bytes: &mut [u8], offset: usize, value: u32| {
        bytes[offset..offset + 4].copy_from_slice(&value.to_le_bytes())
    };
    let wide = |bytes: &mut [u8], offset: usize, value: u64| {
        bytes[offset..offset + 8].copy_from_slice(&value.to_le_bytes())
    };
    for (offset, value) in [
        (0, 0xfeed_facf),
        (4, 0x0100_000c),
        (12, 2),
        (16, 2),
        (20, 184),
        (32, 0x19),
        (36, 152),
        (88, 5),
        (92, 5),
        (96, 1),
        (152, 256),
        (156, 3),
        (184, 0xe),
        (188, 32),
        (192, 12),
    ] {
        put(&mut image, offset, value);
    }
    let text = *b"__TEXT\0\0\0\0\0\0\0\0\0\0";
    image[40..56].copy_from_slice(&text);
    image[104..120].copy_from_slice(b"__trust_pairqual");
    image[120..136].copy_from_slice(&text);
    wide(&mut image, 56, 0x100000000);
    wide(&mut image, 64, 320);
    wide(&mut image, 80, 320);
    wide(&mut image, 136, 0x100000100);
    wide(&mut image, 144, 64);
    image[196..209].copy_from_slice(b"/usr/lib/dyld");
    image[256..320].copy_from_slice(&paired::PAIRED_PROTOCOL_MARKER);
    image[256..272].copy_from_slice(b"TRUSTPAIRQUAL001");
    std::fs::write(&program, &image).unwrap();
    std::fs::set_permissions(&program, std::fs::Permissions::from_mode(0o555)).unwrap();
    let deadline = Instant::now() + Duration::from_secs(30);
    let old = pair::file_identity(&program).unwrap();
    // First prove the actual held file passes the ordinary input profile;
    // failure below is specifically its old protocol, never a spawn failure.
    trust_resource_provenance::program::HeldProgram::open(
        &root,
        &program,
        &decode(old.sha256.as_bytes()).unwrap(),
        deadline,
    )
    .unwrap();
    let error = retain_input_program(&root, &old, deadline).err().unwrap();
    assert!(error.0.contains("protocol"), "{error}");
    image[256..320].copy_from_slice(&paired::PAIRED_PROTOCOL_MARKER);
    std::fs::set_permissions(&program, std::fs::Permissions::from_mode(0o755)).unwrap();
    std::fs::write(&program, &image).unwrap();
    std::fs::set_permissions(&program, std::fs::Permissions::from_mode(0o555)).unwrap();
    let current = pair::file_identity(&program).unwrap();
    let input = retain_input_program(&root, &current, deadline).unwrap();
    input.validate(deadline).unwrap();
    std::fs::rename(&program, root.join("bin/original")).unwrap();
    std::fs::write(&program, &image).unwrap();
    std::fs::set_permissions(&program, std::fs::Permissions::from_mode(0o555)).unwrap();
    assert!(
        input.validate(deadline).is_err(),
        "replacement bytes do not recreate the original input owner"
    );
}
