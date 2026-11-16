use super::*;

fn linker() -> Request {
    let mut request = request();
    request.role = Role::MachOLinker(Loan { parent_attempt: [4; 16], nonce: [5; 16], cpu_slot: 0 });
    request.command.program = b"/sdk/bin/rust-lld".to_vec();
    request.command.args = [
        "-flavor",
        "darwin",
        "input.o",
        "-o",
        "output",
        "--threads=1",
        "--thinlto-jobs=1",
        "--read-workers=0",
    ]
    .into_iter()
    .map(|value| value.as_bytes().to_vec())
    .collect();
    request.delegations.gnu = GnuTransport::None;
    request
}

#[test]
fn linker_loan_roundtrip_preserves_parent_nonce_and_existing_cpu_shape() {
    let request = linker();
    let bytes = request.encode().unwrap();
    assert!(Request::decode(&bytes).unwrap() == request);
    for end in 0..bytes.len() {
        assert!(Request::decode(&bytes[..end]).is_err());
    }
    let mut reserved_metadata = bytes.clone();
    let position = reserved_metadata
        .windows(request.member_attempt.len())
        .position(|value| value == request.member_attempt)
        .unwrap();
    let role_offset = position + request.member_attempt.len();
    assert_eq!(
        &reserved_metadata[role_offset..role_offset + 8],
        &MACHO_LINKER_REQUEST_ROLE.to_be_bytes()
    );
    reserved_metadata[role_offset..role_offset + 8].copy_from_slice(&3u64.to_be_bytes());
    assert!(Request::decode(&reserved_metadata).is_err());
    let mut overflow = bytes.clone();
    let nonce = [5; 16];
    let position = overflow.windows(nonce.len()).position(|value| value == nonce).unwrap();
    overflow[position + nonce.len()..position + nonce.len() + 8]
        .copy_from_slice(&u64::MAX.to_le_bytes());
    assert!(Request::decode(&overflow).is_err());
    let mut extra = bytes;
    extra.push(0);
    assert!(Request::decode(&extra).is_err());
    for parent_attempt in [[0; 16], request.binding.root_attempt, request.member_attempt] {
        let mut invalid = linker();
        invalid.role = Role::MachOLinker(Loan { parent_attempt, nonce: [5; 16], cpu_slot: 0 });
        assert!(invalid.encode().is_err());
    }
    let mut invalid = linker();
    invalid.role = Role::MachOLinker(Loan { parent_attempt: [4; 16], nonce: [0; 16], cpu_slot: 0 });
    assert!(invalid.encode().is_err());
}

#[test]
fn linker_loan_refuses_extra_backing_opaque_response_and_missing_final_limits() {
    let mut invalid = linker();
    invalid.delegations.cpu = None;
    assert!(invalid.encode().is_err());
    let mut invalid = linker();
    invalid.delegations.gnu = request().delegations.gnu;
    assert!(invalid.encode().is_err());
    let mut invalid = linker();
    invalid.delegations.fences.push(Descriptor { source: 8, target: 9 });
    assert!(invalid.encode().is_err());
    for (index, value) in [
        (1, "elf"),
        (2, "@/private/args"),
        (5, "--threads=2"),
        (6, "--thinlto-jobs=2"),
        (7, "--read-workers=1"),
    ] {
        let mut invalid = linker();
        invalid.command.args[index] = value.as_bytes().to_vec();
        assert!(invalid.encode().is_err());
    }
    let mut invalid = linker();
    invalid.command.args.push(b"--threads=28".to_vec());
    assert!(invalid.encode().is_err());
    // Shape acceptance does not certify every linker option as safe. The Host
    // must independently enforce its pinned paired-linker recipe before ARM.
}
