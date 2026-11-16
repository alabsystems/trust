use super::*;
use crate::Status;
use crate::accounting::{CpuTimes, Observation};
use crate::workload::host::census::SourceKind;

fn pages() -> Pages {
    Pages {
        root_attempt: [1; 16],
        invocation_sha256: [2; 32],
        snapshot: [3; 16],
        offset: 0,
        total: None,
        seen: BTreeSet::new(),
        failed: false,
    }
}
fn entry(id: u8, known_zero: bool) -> Entry {
    Entry {
        member_attempt: [id; 16],
        kind: SourceKind::Query,
        identity: None,
        started: None,
        terminal: Status::Refused { reason: "saved diagnostic only".into() },
        accounting: Observation {
            cpu_times: known_zero.then_some(CpuTimes { user_ns: 0, system_ns: 0 }),
            ..Observation::uncollected()
        },
        retired: false,
        drained: true,
    }
}

#[test]
fn contiguous_variable_pages_retain_every_missing_and_zero_observation_until_complete() {
    let mut pages = pages();
    assert_eq!(pages.total, None);
    assert!(!pages.complete());
    let first = pages
        .accept(Page { request: pages.request(), total: 3, entries: vec![entry(4, true)] })
        .unwrap();
    assert_eq!(first.len(), 1);
    assert_eq!(first[0].accounting.cpu_times, Some(CpuTimes { user_ns: 0, system_ns: 0 }));
    assert_eq!(pages.total, Some(3));
    assert_eq!(pages.offset, 1);
    assert!(!pages.complete());
    let second = pages
        .accept(Page {
            request: pages.request(),
            total: 3,
            entries: vec![entry(5, false), entry(6, false)],
        })
        .unwrap();
    assert_eq!(second.len(), 2);
    assert_eq!(second[0].accounting.cpu_times, None);
    assert_eq!(pages.offset, 3);
    assert_eq!(pages.seen.len(), 3);
    assert!(pages.complete());
    assert!(
        pages.accept(Page { request: pages.request(), total: 3, entries: Vec::new() }).is_err()
    );
    assert!(!pages.complete());
}

#[test]
fn changed_nonce_total_skipped_offsets_or_cross_page_duplicates_poison_without_shrinking() {
    for changed in 0..4 {
        let mut pages = pages();
        pages
            .accept(Page { request: pages.request(), total: 3, entries: vec![entry(4, false)] })
            .unwrap();
        let mut next = Page { request: pages.request(), total: 3, entries: vec![entry(5, false)] };
        match changed {
            0 => next.request.snapshot = [9; 16],
            1 => next.request.offset += 1,
            2 => next.total = 2,
            _ => next.entries[0].member_attempt = [4; 16],
        }
        assert!(pages.accept(next).is_err());
        assert!(pages.failed);
        assert!(!pages.complete());
        assert_eq!(pages.offset, 1);
        assert_eq!(pages.total, Some(3));
    }
}
