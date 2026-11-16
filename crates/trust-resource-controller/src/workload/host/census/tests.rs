use super::*;
use crate::accounting::CpuTimes;
use crate::{CompletionCause, Outcome};

fn request(offset: u32) -> Request {
    Request { root_attempt: [1; 16], invocation_sha256: [2; 32], snapshot: [3; 16], offset }
}
fn entry(id: u8, kind: SourceKind) -> Entry {
    // Saved codec facts only: these do not claim a real host/child/SDK run.
    let identity = Identity { pid: 42, birth: 9, birth_kind: BirthKind::MacosWallMicroseconds };
    Entry {
        member_attempt: [id; 16],
        kind,
        identity: Some(identity),
        started: Some(Started { identity, monotonic_ns: 100, unix_ns: 200 }),
        terminal: Status::Finished {
            outcome: Outcome::Signal(9),
            cause: CompletionCause::Cancelled,
            runtime_ns: 99,
        },
        accounting: Observation {
            cpu_times: Some(CpuTimes { user_ns: 0, system_ns: 0 }),
            peak_rss_bytes: Some(0),
            ..Observation::uncollected()
        },
        retired: true,
        drained: true,
    }
}
fn page() -> Reply {
    Reply::Page(Page {
        request: request(0),
        total: 6,
        entries: [
            SourceKind::Compiler,
            SourceKind::Linker,
            SourceKind::Query,
            SourceKind::BuildScript,
            SourceKind::Inventory,
            SourceKind::Sample,
        ]
        .into_iter()
        .enumerate()
        .map(|(i, kind)| entry(i as u8 + 4, kind))
        .collect(),
    })
}

#[test]
fn complete_all_role_data_retains_native_status_scope_and_observed_zero_without_authority() {
    let original = page();
    let bytes = original.encode().unwrap();
    assert_eq!(Reply::decode(&bytes, &request(0)).unwrap(), original);
    let req = request(0).encode().unwrap();
    assert_eq!(Request::decode(&req).unwrap(), request(0));
    assert!(crate::Request::decode(&req).is_err());
    assert!(crate::Call::decode(&req).is_err());
    assert!(super::super::phase::Request::decode(&req).is_err());
    assert!(super::super::bank::Request::decode(&bytes).is_err());
    for original in [
        Reply::Busy { request: request(0) },
        Reply::Refused { request: request(0), reason: "actual host not quiescent".into() },
    ] {
        assert_eq!(Reply::decode(&original.encode().unwrap(), &request(0)).unwrap(), original);
    }
}

#[test]
fn unknown_and_refused_keep_missing_measurement_identity_and_retirement_facts_explicit() {
    let mut unknown = entry(4, SourceKind::Compiler);
    unknown.terminal =
        Status::Unknown { reason: "original status unavailable".into(), started: unknown.started };
    unknown.accounting = Observation::uncollected();
    unknown.retired = false;
    unknown.drained = false;
    let refused = Entry {
        member_attempt: [5; 16],
        kind: SourceKind::Query,
        identity: None,
        started: None,
        terminal: Status::Refused { reason: "before target delivery".into() },
        accounting: Observation::uncollected(),
        retired: false,
        drained: true,
    };
    let original =
        Reply::Page(Page { request: request(0), total: 2, entries: vec![unknown, refused] });
    assert_eq!(Reply::decode(&original.encode().unwrap(), &request(0)).unwrap(), original);
    let Reply::Page(mut invalid) = original else { unreachable!() };
    invalid.entries[0].accounting.cpu_times = Some(CpuTimes { user_ns: 0, system_ns: 0 });
    assert!(Reply::Page(invalid).encode().is_err(), "Unknown is not a measured zero");
}

#[test]
fn snapshot_binding_missing_bytes_duplicate_attempts_and_inconsistent_lifecycle_refuse() {
    let bytes = page().encode().unwrap();
    for changed in 0..4 {
        let mut wrong = request(0);
        match changed {
            0 => wrong.root_attempt = [9; 16],
            1 => wrong.invocation_sha256 = [9; 32],
            2 => wrong.snapshot = [9; 16],
            _ => wrong.offset = 1,
        }
        assert!(Reply::decode(&bytes, &wrong).is_err());
    }
    for length in 0..bytes.len() {
        assert!(Reply::decode(&bytes[..length], &request(0)).is_err());
    }
    let mut trailing = bytes;
    trailing.push(0);
    assert!(Reply::decode(&trailing, &request(0)).is_err());
    for changed in 0..8 {
        let Reply::Page(mut invalid) = page() else { unreachable!() };
        match changed {
            0 => invalid.total = MAX_ENTRIES + 1,
            1 => invalid.entries[1].member_attempt = invalid.entries[0].member_attempt,
            2 => invalid.entries[0].member_attempt = request(0).root_attempt,
            3 => invalid.entries[0].identity = None,
            4 => invalid.entries[0].terminal = Status::Attached,
            5 => invalid.entries[0].started = None,
            6 => invalid.entries[0].terminal = Status::Refused { reason: "late".into() },
            _ => invalid.entries.clear(),
        }
        assert!(Reply::Page(invalid).encode().is_err(), "changed{changed}");
    }
}

#[test]
fn population_and_original_frame_bounds_apply_before_any_whole_census_allocation() {
    let entries: Vec<_> = (0..MAX_PAGE_ENTRIES + 1)
        .map(|index| {
            let mut value = entry(4, SourceKind::Compiler);
            value.member_attempt[..8].copy_from_slice(&(index as u64 + 10).to_be_bytes());
            value
        })
        .collect();
    assert!(Reply::Page(Page { request: request(0), total: 129, entries }).encode().is_err());
    let entries: Vec<_> = (0..32)
        .map(|index| {
            let mut value = entry(index + 4, SourceKind::Compiler);
            value.identity = None;
            value.started = None;
            value.accounting = Observation::uncollected();
            value.terminal = Status::Refused { reason: "x".repeat(crate::MAX_FIELD) };
            value
        })
        .collect();
    assert!(Reply::Page(Page { request: request(0), total: 32, entries }).encode().is_err());
    let empty = Reply::Page(Page { request: request(0), total: 0, entries: Vec::new() });
    assert_eq!(Reply::decode(&empty.encode().unwrap(), &request(0)).unwrap(), empty);
}
