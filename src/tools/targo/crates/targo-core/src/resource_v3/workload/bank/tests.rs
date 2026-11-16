use super::*;

use std::num::NonZeroU32;
use std::os::fd::AsRawFd;
use std::sync::atomic::{AtomicU32, AtomicUsize};
use trust_build_cpu::{Owner, Pool};
use trust_resource_controller::BirthKind;

#[test]
fn large_original_bank_obeys_live_policy_without_seven_worker_cap() {
    let fixture = Fixture::new(28, 28);
    let mut loans = Vec::new();
    for _ in 0..28 {
        loans.push(fixture.bank.try_primary().unwrap().unwrap());
    }
    assert!(fixture.bank.try_primary().unwrap().is_none());
    assert!(
        fixture
            .pool
            .try_acquire(Owner::current(None))
            .unwrap()
            .is_none()
    );
    fixture.limit.store(10, Ordering::Release);
    loans.truncate(9);
    assert!(fixture.bank.try_primary().unwrap().is_some());
    fixture.limit.store(9, Ordering::Release);
    assert!(fixture.bank.try_primary().unwrap().is_none());
    fixture.limit.store(28, Ordering::Release);
    assert!(fixture.bank.try_primary().unwrap().is_some());
    // Dynamic policy changes lend only the same retained original guards.
    assert!(
        fixture
            .pool
            .try_acquire(Owner::current(None))
            .unwrap()
            .is_none()
    );
}

#[test]
fn initial_pair_allows_only_closed_queries_before_output_and_gnu_custody() {
    let directory = tempfile::tempdir().unwrap();
    let pool = Pool::open_in(directory.path(), NonZeroU32::new(3).unwrap()).unwrap();
    let lease = pool.try_acquire(Owner::current(None)).unwrap().unwrap();
    let meta = std::fs::File::from(lease.as_fd().try_clone_to_owned().unwrap())
        .metadata()
        .unwrap();
    let bank = RootCreditBank::retained_initial(
        vec![Original {
            lease: Arc::new(lease),
            backing: FileIdentity {
                device: meta.dev(),
                inode: meta.ino(),
            },
        }],
        [1; 16],
        [2; 32],
        InitialRestriction {
            width: 3,
            ceiling: 3,
            phase: [3; 16],
        },
        Arc::new(|_| 3),
    )
    .unwrap();
    assert_eq!(bank.funded_width().unwrap(), 1);
    assert!(!bank.fully_funded().unwrap());
    assert!(bank.try_primary().unwrap().is_none());
    let query = bank.try_query().unwrap().unwrap();
    assert!(
        bank.try_query().unwrap().is_none(),
        "one actual initial implicit pair"
    );
    assert!(
        bank.initial_ready().unwrap().is_none(),
        "active query prevents GNU preparation"
    );
    assert!(
        query.begin_compiler([4; 16]).is_err(),
        "query reservation cannot become producing work"
    );
    assert!(query.require_preparation(&query.lease()).is_err());
    query.begin_query([4; 16]).unwrap();
    query.before_request().unwrap();
    drop(query);
    assert!(bank.initial_ready().unwrap().is_some());
    bank.park_initial_output().unwrap();
    assert!(bank.try_query().unwrap().is_none());
    assert!(bank.try_primary().unwrap().is_none());
    assert!(
        pool.try_acquire(Owner::current(None)).unwrap().is_some(),
        "declared maximum did not acquire the other native units"
    );
    // Actual private kernel conservation only, no authenticated SDK/Host.
}

#[test]
fn cancelling_idle_probe_preserves_an_enclosing_dispatch_park() {
    let fixture = Fixture::new(3, 3);
    assert!(fixture.bank.begin_partial_probe().unwrap().is_some());
    fixture.bank.park().unwrap();
    fixture.bank.cancel_partial_probe().unwrap();
    assert!(fixture.bank.try_primary().unwrap().is_none());
    assert!(fixture.bank.try_query().unwrap().is_none());
    assert!(fixture.bank.current_drained().unwrap());
}

#[test]
fn partial_probe_excludes_real_supplementary_borrows_without_returning_any_capacity() {
    let fixture = Fixture::new(3, 3);
    let implicit = fixture.bank.try_primary().unwrap().unwrap();
    let extra = fixture.bank.try_primary().unwrap().unwrap();
    let borrowed = extra.lease();
    assert!(fixture.bank.begin_partial_probe().unwrap().is_none());
    drop(extra);
    assert!(
        fixture.bank.begin_partial_probe().unwrap().is_none(),
        "a real borrowed native description outlives its logical reservation"
    );
    drop(borrowed);
    let original = fixture.bank.begin_partial_probe().unwrap().unwrap();
    assert_eq!(original.slot, implicit.lease().slot());
    assert!(fixture.bank.try_primary().unwrap().is_none());
    assert!(
        fixture
            .pool
            .try_acquire(Owner::current(None))
            .unwrap()
            .is_none(),
        "negative preparation alone never releases a native guard"
    );
    fixture.bank.cancel_partial_probe().unwrap();
    assert!(fixture.bank.fully_funded().unwrap());
    assert!(fixture.bank.try_primary().unwrap().is_some());
    drop(implicit);
}

#[test]
fn ordinary_or_foreign_primary_cannot_promote_itself_to_local_publication() {
    let fixture = Fixture::new(2, 2);
    let other = Fixture::new(2, 2);
    let primary = fixture.bank.try_primary().unwrap().unwrap();
    assert_eq!(fixture.bank.lock().unwrap().occupied(), 1);
    assert!(fixture.bank.try_coordinator_local(&primary).is_err());
    assert!(other.bank.try_coordinator_local(&primary).is_err());
    assert_eq!(fixture.bank.lock().unwrap().occupied(), 1);
    assert_eq!(other.bank.lock().unwrap().occupied(), 0);
    assert!(fixture.bank.lock().unwrap().local_cancel.is_none());
    // The original funded kernel descriptions remain conserved; these
    // negative controls create no SDK/coordinator/Ready stand-in.
    assert!(
        fixture
            .pool
            .try_acquire(Owner::current(None))
            .unwrap()
            .is_none()
    );
    drop(primary);
    assert_eq!(fixture.bank.lock().unwrap().occupied(), 0);
}

struct Fixture {
    _directory: tempfile::TempDir,
    pool: Pool,
    bank: Arc<RootCreditBank>,
    limit: Arc<AtomicU32>,
}
impl Fixture {
    fn new(width: u32, ceiling: u32) -> Self {
        Self::new_in(width, ceiling, None)
    }

    fn new_in(width: u32, ceiling: u32, parent: Option<&std::path::Path>) -> Self {
        // A genuine private native pool, not a production host/SDK fixture.
        // These actual kernel guards exercise conservation; they grant no
        // eligibility to run the real workload or construct authenticated startup.
        let directory = match parent {
            Some(parent) => tempfile::tempdir_in(parent).unwrap(),
            None => tempfile::tempdir().unwrap(),
        };
        let pool = Pool::open_in(directory.path(), NonZeroU32::new(width).unwrap()).unwrap();
        let mut originals = Vec::new();
        for _ in 0..width {
            let lease = pool.try_acquire(Owner::current(None)).unwrap().unwrap();
            let meta = std::fs::File::from(lease.as_fd().try_clone_to_owned().unwrap())
                .metadata()
                .unwrap();
            originals.push(Original {
                lease: Arc::new(lease),
                backing: FileIdentity {
                    device: meta.dev(),
                    inode: meta.ino(),
                },
            });
        }
        let limit = Arc::new(AtomicU32::new(ceiling));
        let policy = limit.clone();
        let bank = RootCreditBank::retained(
            originals,
            [1; 16],
            [2; 32],
            ceiling,
            Arc::new(move |_| policy.load(Ordering::Acquire)),
        )
        .unwrap();
        Self {
            _directory: directory,
            pool,
            bank,
            limit,
        }
    }

    fn request(&self, sequence: u64, operation: bank::Operation) -> bank::Request {
        bank::Request {
            key: bank::Key {
                root_attempt: [1; 16],
                invocation_sha256: [2; 32],
                sequence,
            },
            operation,
        }
    }

    fn primary(&self, member: u8) -> Arc<PrimaryLoan> {
        let primary = self.bank.try_primary().unwrap().unwrap();
        primary.begin_compiler([member; 16]).unwrap();
        primary
    }

    fn grant_primary(&self, primary: &PrimaryLoan, sequence: u64, member: u8) -> Attempt {
        let request = self.request(
            sequence,
            bank::Operation::Primary {
                member_attempt: [member; 16],
                slot: primary.lease().slot(),
            },
        );
        let answer = self.bank.handle(&request).unwrap();
        bank::Reply::decode(&answer.reply.encode().unwrap(), &request).unwrap();
        let bank::Decision::Granted {
            loan,
            slot,
            backing,
            ..
        } = answer.reply.decision
        else {
            panic!("funded primary did not receive its original slot")
        };
        let original = answer.original.unwrap();
        assert_eq!(
            original.as_raw_fd(),
            primary.lease().as_raw_fd(),
            "the SAME original FD is lent"
        );
        assert_eq!(slot, original.slot());
        let actual = std::fs::File::from(original.as_fd().try_clone_to_owned().unwrap())
            .metadata()
            .unwrap();
        assert_eq!(
            backing,
            FileIdentity {
                device: actual.dev(),
                inode: actual.ino()
            }
        );
        loan
    }

    fn returned(&self, sequence: u64, member: u8, loan: Attempt, slot: u32) {
        let answer = self
            .bank
            .handle(&self.request(
                sequence,
                bank::Operation::Returned {
                    member_attempt: [member; 16],
                    loan,
                    slot,
                },
            ))
            .unwrap();
        assert_eq!(answer.reply.decision, bank::Decision::Returned);
        assert!(answer.original.is_none());
    }
}

fn producer() -> Identity {
    Identity {
        pid: 42,
        birth: 10,
        birth_kind: if cfg!(target_os = "macos") {
            BirthKind::MacosWallMicroseconds
        } else {
            BirthKind::LinuxStartTicks
        },
    }
}

#[test]
fn retained_compiler_loan_observes_both_actual_bank_returns_without_reopening_it() {
    for host_first in [false, true] {
        // Actual private kernel originals test conservation of the bank
        // component only. This fabricates no hosted target/SDK/EOF receipt.
        let fixture = Fixture::new(1, 1);
        let primary = fixture.primary(3);
        let loan = fixture.grant_primary(&primary, 1, 3);
        assert!(primary.require_closed_compiler([3; 16]).is_err());
        if host_first {
            fixture.returned(2, 3, loan, primary.lease().slot());
            assert!(primary.require_closed_compiler([3; 16]).is_err());
            primary.retired().unwrap();
        } else {
            primary.retired().unwrap();
            assert_eq!(
                primary.require_closed_compiler([3; 16]).unwrap_err().kind(),
                io::ErrorKind::WouldBlock
            );
            assert!(fixture.bank.try_primary().unwrap().is_none());
            fixture.returned(2, 3, loan, primary.lease().slot());
        }
        primary.require_closed_compiler([3; 16]).unwrap();
        assert!(primary.require_closed_compiler([4; 16]).is_err());
        let next = fixture.bank.try_primary().unwrap().unwrap();
        next.require_preparation(&next.lease()).unwrap();
        primary.require_closed_compiler([3; 16]).unwrap();
        assert!(
            primary.require_preparation(&primary.lease()).is_err(),
            "closed original cannot fund new kernel preparation"
        );
        assert!(
            fixture
                .pool
                .try_acquire(Owner::current(None))
                .unwrap()
                .is_none(),
            "logical closure never drops/reacquires the original kernel guard"
        );
        drop(next);
    }
}

#[test]
fn preparation_observation_preserves_original_reservation_and_refuses_alias_or_bound_member() {
    let fixture = Fixture::new(1, 1);
    let reserved = fixture.bank.try_primary().unwrap().unwrap();
    let original = reserved.lease();
    reserved.require_preparation(&original).unwrap();
    reserved.require_preparation(&original).unwrap();
    assert!(fixture.bank.try_primary().unwrap().is_none());
    let alias = Arc::new(original.try_clone().unwrap());
    assert!(reserved.require_preparation(&alias).is_err());
    assert!(fixture.bank.try_primary().unwrap().is_none());
    reserved.begin_query([3; 16]).unwrap();
    assert!(reserved.require_preparation(&original).is_err());
    reserved.before_request().unwrap();
    assert!(reserved.require_preparation(&original).is_err());
    let another = fixture.bank.try_primary().unwrap().unwrap();
    another.require_preparation(&another.lease()).unwrap();
    fixture.bank.park().unwrap();
    assert!(another.require_preparation(&another.lease()).is_err());
    assert_eq!(fixture.bank.lock().unwrap().occupied(), 1);
    drop(another);
    assert!(fixture.bank.is_drained().unwrap());
}

#[test]
fn empty_current_table_never_erases_an_earlier_compiler_binding_for_output_custody() {
    let fixture = Fixture::new(2, 2);
    assert!(fixture.bank.before_compilation().unwrap());
    let query = fixture.bank.try_primary().unwrap().unwrap();
    query.begin_query([3; 16]).unwrap();
    query.before_request().unwrap();
    assert!(fixture.bank.before_compilation().unwrap());
    let compiler = fixture.bank.try_primary().unwrap().unwrap();
    compiler.begin_compiler([4; 16]).unwrap();
    compiler.before_request().unwrap();
    fixture.bank.park().unwrap();
    assert!(fixture.bank.is_drained().unwrap());
    assert!(
        !fixture.bank.before_compilation().unwrap(),
        "drained is not precompile authorization"
    );
}

#[test]
fn cached_live_policy_receives_actual_busy_loans_instead_of_the_full_held_domain() {
    let mut fixture = Fixture::new(8, 3);
    let observed = Arc::new(Mutex::new(Vec::new()));
    let calls = observed.clone();
    Arc::get_mut(&mut fixture.bank).unwrap().live_limit = Arc::new(move |busy| {
        calls.lock().unwrap().push(busy);
        3
    });
    let primary = fixture.primary(3);
    let queued = fixture.bank.try_primary().unwrap().unwrap();
    let id = fixture.grant_primary(&primary, 1, 3);
    let answer = fixture
        .bank
        .handle(&fixture.request(
            2,
            bank::Operation::Extra {
                member_attempt: [3; 16],
                worker_request: [4; 16],
                producer: producer(),
            },
        ))
        .unwrap();
    assert_eq!(*observed.lock().unwrap(), [0, 1, 2]);
    let bank::Decision::Granted { loan, slot, .. } = answer.reply.decision else {
        panic!("extra")
    };
    fixture.returned(3, 3, loan, slot);
    fixture.returned(4, 3, id, primary.lease().slot());
    primary.retired().unwrap();
    drop(queued);
    assert_eq!(
        *observed.lock().unwrap(),
        [0, 1, 2],
        "returns/continuations never apply fresh admission"
    );
    fixture.bank.park().unwrap();
    assert!(fixture.bank.is_drained().unwrap());
}

#[test]
fn full_actual_reservation_is_distinct_from_dispatch_and_physical_slots_stay_held() {
    let fixture = Fixture::new(4, 2);
    assert!(
        fixture
            .pool
            .try_acquire(Owner::current(None))
            .unwrap()
            .is_none()
    );
    let a = fixture.bank.try_primary().unwrap().unwrap();
    let b = fixture.bank.try_primary().unwrap().unwrap();
    assert_ne!(a.lease().slot(), b.lease().slot());
    assert!(
        fixture.bank.try_primary().unwrap().is_none(),
        "reserved four does not dispatch four"
    );
    drop(a);
    let c = fixture.bank.try_primary().unwrap().unwrap();
    drop((b, c));
    assert!(
        fixture
            .pool
            .try_acquire(Owner::current(None))
            .unwrap()
            .is_none(),
        "logical returns never release/reacquire the original actual guards"
    );
    fixture.bank.park().unwrap();
    assert!(fixture.bank.is_drained().unwrap());
}

#[test]
fn primaries_and_compiler_extras_share_one_held_table_and_live_memory_cpu_ceiling() {
    let fixture = Fixture::new(4, 3);
    let primary = fixture.primary(3);
    let primary_id = fixture.grant_primary(&primary, 1, 3);
    let queued = fixture.bank.try_primary().unwrap().unwrap();
    let request = fixture.request(
        2,
        bank::Operation::Extra {
            member_attempt: [3; 16],
            worker_request: [4; 16],
            producer: producer(),
        },
    );
    let answer = fixture.bank.handle(&request).unwrap();
    let bank::Decision::Granted { loan, slot, .. } = answer.reply.decision else {
        panic!("extra")
    };
    assert_ne!(slot, primary.lease().slot());
    assert_ne!(slot, queued.lease().slot());
    assert!(fixture.bank.try_primary().unwrap().is_none());
    fixture.limit.store(2, Ordering::Release);
    let busy = fixture
        .bank
        .handle(&fixture.request(
            3,
            bank::Operation::Extra {
                member_attempt: [3; 16],
                worker_request: [5; 16],
                producer: producer(),
            },
        ))
        .unwrap();
    assert_eq!(busy.reply.decision, bank::Decision::Busy);
    assert!(busy.original.is_none());
    fixture.returned(4, 3, loan, slot);
    assert!(
        fixture.bank.try_primary().unwrap().is_none(),
        "current lower ceiling still vetoes NEW work"
    );
    drop(queued);
    fixture.limit.store(0, Ordering::Release);
    assert!(fixture.bank.try_primary().unwrap().is_none());
    // An existing funded primary may complete under a fresh zero veto.
    fixture.returned(5, 3, primary_id, primary.lease().slot());
    primary.retired().unwrap();
    fixture.bank.park().unwrap();
    assert!(fixture.bank.is_drained().unwrap());
}

#[test]
fn compiler_materialization_requires_its_original_success_and_cannot_replace_host_return() {
    use trust_resource_controller::{CompletionCause, Outcome, Status};
    let successful = Status::Finished {
        outcome: Outcome::Exit(0),
        cause: CompletionCause::Exited,
        runtime_ns: 1,
    };
    let fixture = Fixture::new(1, 1);
    let primary = fixture.primary(3);
    assert!(primary.record_compiler_terminal(&successful).is_err());
    assert_eq!(primary.retired_compiler_attempt(), None);
    assert_eq!(primary.completed_compiler(), None);
    assert!(primary.successful_job_compiler().is_err());
    let id = fixture.grant_primary(&primary, 1, 3);
    assert_eq!(primary.retired_compiler_attempt(), None);
    primary.retired().unwrap();
    for (outcome, cause) in [
        (Outcome::Exit(7), CompletionCause::Exited),
        (Outcome::Signal(9), CompletionCause::Exited),
        (Outcome::Exit(0), CompletionCause::Timeout),
        (Outcome::Exit(0), CompletionCause::Cancelled),
        (Outcome::Exit(0), CompletionCause::ResourceLimit),
        (Outcome::Exit(0), CompletionCause::HostFault),
    ] {
        primary
            .record_compiler_terminal(&Status::Finished {
                outcome,
                cause,
                runtime_ns: 1,
            })
            .unwrap();
        assert_eq!(primary.completed_compiler(), None);
        assert_eq!(
            primary.retired_compiler_attempt(),
            Some([3; 16]),
            "known failed retirement ends reads without creating a successful producer"
        );
    }
    primary.record_compiler_terminal(&successful).unwrap();
    assert_eq!(primary.completed_compiler(), Some([3; 16]));
    assert_eq!(primary.successful_job_compiler().unwrap(), Some([3; 16]));
    assert!(primary.record_compiler_terminal(&successful).is_err());
    fixture.bank.park().unwrap();
    assert!(
        !fixture.bank.is_drained().unwrap(),
        "receipt never supplies host retirement"
    );
    fixture.returned(2, 3, id, primary.lease().slot());
    assert!(fixture.bank.is_drained().unwrap());

    let never_delivered = Fixture::new(1, 1);
    let primary = never_delivered.primary(4);
    primary.before_request().unwrap();
    assert!(primary.record_compiler_terminal(&successful).is_err());
    assert_eq!(primary.completed_compiler(), None);
    assert!(primary.successful_job_compiler().is_err());
}

#[test]
fn positive_host_return_and_original_helper_retirement_are_both_required_in_either_order() {
    for host_first in [false, true] {
        let fixture = Fixture::new(1, 1);
        let primary = fixture.primary(3);
        let id = fixture.grant_primary(&primary, 1, 3);
        let slot = primary.lease().slot();
        if host_first {
            fixture.returned(2, 3, id, slot);
        } else {
            primary.retired().unwrap();
        }
        let primary = if host_first {
            Some(primary)
        } else {
            // The local owner may disappear before the asynchronous host
            // Return; the SAME bank must retain its still-busy logical loan.
            drop(primary);
            None
        };
        assert!(
            fixture.bank.try_primary().unwrap().is_none(),
            "first fact cannot return the credit"
        );
        fixture.bank.park().unwrap();
        assert!(!fixture.bank.is_drained().unwrap());
        if host_first {
            primary.as_ref().unwrap().retired().unwrap();
        } else {
            fixture.returned(2, 3, id, slot);
        }
        assert!(fixture.bank.is_drained().unwrap());
        fixture.bank.resume().unwrap();
        assert!(fixture.bank.try_primary().unwrap().is_some());
    }
}

#[test]
fn park_blocks_new_primaries_and_extras_but_preserves_current_positive_return_path() {
    let fixture = Fixture::new(3, 3);
    let primary = fixture.primary(3);
    let id = fixture.grant_primary(&primary, 1, 3);
    fixture.bank.park().unwrap();
    assert!(fixture.bank.try_primary().unwrap().is_none());
    assert!(!fixture.bank.is_drained().unwrap());
    assert!(fixture.bank.resume().is_err());
    let busy = fixture
        .bank
        .handle(&fixture.request(
            2,
            bank::Operation::Extra {
                member_attempt: [3; 16],
                worker_request: [4; 16],
                producer: producer(),
            },
        ))
        .unwrap();
    assert_eq!(busy.reply.decision, bank::Decision::Busy);
    primary.retired().unwrap();
    fixture.returned(3, 3, id, primary.lease().slot());
    assert!(fixture.bank.is_drained().unwrap());
}

#[test]
fn affirmative_before_request_cancels_only_the_original_unexposed_primary() {
    let fixture = Fixture::new(1, 1);
    let primary = fixture.primary(3);
    primary.before_request().unwrap();
    assert!(primary.before_request().is_err());
    assert!(fixture.bank.try_primary().unwrap().is_some());
    let next = fixture.primary(4);
    fixture.grant_primary(&next, 1, 4);
    assert!(
        next.before_request().is_err(),
        "delivered startup custody cannot become BeforeRequest"
    );
    next.retired().unwrap();
    // This local retirement has not fabricated the host's positive return.
    fixture.bank.park().unwrap();
    assert!(!fixture.bank.is_drained().unwrap());
    fixture.returned(2, 4, next.loan, next.lease().slot());
    assert!(fixture.bank.is_drained().unwrap());
}

#[test]
fn query_and_compiler_borrow_the_same_original_table_with_distinct_member_purposes() {
    let fixture = Fixture::new(1, 1);
    let query = fixture.bank.try_primary().unwrap().unwrap();
    query.begin_query([3; 16]).unwrap();
    assert!(query.belongs_to(&fixture.bank));
    assert!(fixture.bank.try_primary().unwrap().is_none());
    let id = fixture.grant_primary(&query, 1, 3);
    // Component-level explicit retirement, not a fabricated MetadataResult or
    // host execution fixture. The actual query owner still needs55+EOF+pin,
    // and the table additionally waits for the real host's matching Return.
    query.retired().unwrap();
    assert!(fixture.bank.try_primary().unwrap().is_none());
    fixture.returned(2, 3, id, query.lease().slot());
    let compiler = fixture.primary(4);
    assert_eq!(compiler.lease().as_raw_fd(), query.lease().as_raw_fd());
    assert!(query.begin_compiler([5; 16]).is_err());
    compiler.before_request().unwrap();
    fixture.bank.park().unwrap();
    assert!(fixture.bank.is_drained().unwrap());
}

#[test]
fn concurrent_queue_borrowers_never_duplicate_or_exceed_the_actual_policy_width() {
    let fixture = Fixture::new(8, 3);
    let active = AtomicUsize::new(0);
    let maximum = AtomicUsize::new(0);
    let barrier = std::sync::Barrier::new(8);
    std::thread::scope(|scope| {
        for _ in 0..8 {
            scope.spawn(|| {
                barrier.wait();
                for _ in 0..128 {
                    if let Some(primary) = fixture.bank.try_primary().unwrap() {
                        let current = active.fetch_add(1, Ordering::SeqCst) + 1;
                        maximum.fetch_max(current, Ordering::SeqCst);
                        assert!(current <= 3);
                        std::thread::yield_now();
                        active.fetch_sub(1, Ordering::SeqCst);
                        drop(primary);
                    }
                }
            });
        }
    });
    assert!(maximum.load(Ordering::SeqCst) > 0);
    fixture.bank.park().unwrap();
    assert!(fixture.bank.is_drained().unwrap());
}

#[test]
fn foreign_root_invocation_sequence_or_unbound_primary_poisons_without_lending_any_original() {
    for changed in 0..4 {
        let fixture = Fixture::new(1, 1);
        let primary = fixture.bank.try_primary().unwrap().unwrap();
        let mut request = fixture.request(
            1,
            bank::Operation::Primary {
                member_attempt: [3; 16],
                slot: primary.lease().slot(),
            },
        );
        match changed {
            0 => request.key.root_attempt = [9; 16],
            1 => request.key.invocation_sha256 = [9; 32],
            2 => request.key.sequence = 2,
            _ => {}
        }
        assert!(fixture.bank.handle(&request).is_err());
        assert!(fixture.bank.try_primary().is_err());
        drop(primary); // still unoffered; this cannot become an execution abort.
        assert!(
            fixture
                .pool
                .try_acquire(Owner::current(None))
                .unwrap()
                .is_none()
        );
    }
}

#[test]
#[expect(
    clippy::disallowed_methods,
    reason = "native child selects its isolated original-bank abort case before Cargo context exists"
)]
fn native_bound_drop_and_wrong_worker_return_keep_the_original_unknown_abort() {
    const CASE: &str = "TARGO_WORKLOAD_BANK_TEST_CASE";
    const MARKER: &str = "TARGO_WORKLOAD_BANK_TEST_MARKER";
    if let Ok(case) = std::env::var(CASE) {
        let marker = std::path::PathBuf::from(std::env::var_os(MARKER).unwrap());
        // The parent retains this private fixture directory through actual
        // child reap and reclaims it afterwards, even though _exit skips Drop.
        let fixture = Fixture::new_in(2, 2, marker.parent());
        let primary = if case == "query-extra" {
            let query = fixture.bank.try_primary().unwrap().unwrap();
            query.begin_query([3; 16]).unwrap();
            query
        } else {
            fixture.primary(3)
        };
        if case == "wrong-return" {
            fixture.grant_primary(&primary, 1, 3);
            assert!(
                fixture
                    .bank
                    .handle(&fixture.request(
                        2,
                        bank::Operation::Returned {
                            member_attempt: [3; 16],
                            loan: [9; 16],
                            slot: primary.lease().slot(),
                        }
                    ))
                    .is_err()
            );
            assert!(fixture.bank.try_primary().is_err());
        } else if case == "query-extra" {
            fixture.grant_primary(&primary, 1, 3);
            assert!(
                fixture
                    .bank
                    .handle(&fixture.request(
                        2,
                        bank::Operation::Extra {
                            member_attempt: [3; 16],
                            worker_request: [4; 16],
                            producer: producer(),
                        }
                    ))
                    .is_err(),
                "confirmed query cannot borrow compiler workers"
            );
            assert!(fixture.bank.try_primary().is_err());
        } else {
            assert_eq!(case, "bound-drop");
        }
        // Parent requires this exact checked-state marker as well as exit75:
        // a panic during setup cannot masquerade as the expected abort.
        std::fs::write(marker, b"actual-original-bank-checked\n").unwrap();
        drop(primary);
        unreachable!("bound original credit escaped Unknown abort");
    }
    let directory = tempfile::tempdir().unwrap();
    let module = module_path!().split_once("::").unwrap().1;
    let exact = format!(
        "{module}::native_bound_drop_and_wrong_worker_return_keep_the_original_unknown_abort"
    );
    for case in ["bound-drop", "wrong-return", "query-extra"] {
        let marker = directory.path().join(case);
        let status = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", &exact])
            .env(CASE, case)
            .env(MARKER, &marker)
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .status()
            .unwrap();
        assert_eq!(status.code(), Some(75), "{case}");
        assert_eq!(
            std::fs::read(marker).unwrap(),
            b"actual-original-bank-checked\n"
        );
    }
}
