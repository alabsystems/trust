use super::*;

#[test]
fn runtime_idle_escrow_cannot_take_active_tokens_or_refund_on_drop() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("original");
    let name = CString::new(path.as_os_str().as_bytes()).unwrap();
    // SAFETY: the NUL-terminated path is in our owned private directory.
    assert_eq!(unsafe { libc::mkfifo(name.as_ptr(), 0o600) }, 0);
    let original = Jobserver::from_fifo(&path).unwrap();
    for _ in 0..3 {
        original.client().release_raw().unwrap();
    }
    let active = original.client().try_acquire().unwrap().unwrap();
    let mut escrow = IdleTokenEscrow::new(&original, 3).unwrap();
    assert!(!escrow.try_withhold(3).unwrap());
    assert_eq!(escrow.held(), 2);
    assert_eq!(original.client().available().unwrap(), 0);
    active.return_to_server().unwrap();
    assert!(escrow.try_withhold(3).unwrap());
    assert!(escrow.return_backed(4).is_err());
    escrow.return_backed(1).unwrap();
    assert_eq!(original.client().available().unwrap(), 1);
    drop(escrow);
    assert_eq!(original.client().available().unwrap(), 1, "unfunded escrow must not auto-refund");
}

fn width(n: u32) -> NonZeroU32 {
    NonZeroU32::new(n).unwrap()
}

fn coordinator(root: &Path, slots: u32) -> Coordinator {
    Coordinator::open(
        root,
        &root.join("adopted"),
        Requirements::new(None, 4, slots, false, 1).unwrap(),
    )
    .unwrap()
}

fn reserve(queue: &mut Coordinator, maximum: u32) -> Reservation {
    match queue.attempt(Some(1 << 30), maximum).unwrap() {
        Attempt::Admitted(reservation) => reservation,
        Attempt::Waiting(reason) => panic!("fixture could not retain actual locks: {reason:?}"),
    }
}

fn fixture(root: &Path, native: &Path) -> RuntimeFixedClaim {
    let pool = Pool::open_in(native, width(8)).unwrap();
    let mut queue = Coordinator::open(
        root,
        &root.join("adopted"),
        Requirements::new(Some(root.join("worktree.lock")), 4, 1, false, 1).unwrap(),
    )
    .unwrap();
    let claim = reserve(&mut queue, 3).publish_fixed(width(8), width(6)).unwrap();
    RuntimeFixedClaim::new(claim, pool).unwrap()
}

#[test]
fn runtime_lends_only_actual_idle_tokens_and_keeps_the_minimum_share() {
    let root = tempfile::tempdir().unwrap();
    let native = tempfile::tempdir().unwrap();
    let mut runtime = fixture(root.path(), native.path());
    let original = runtime.jobserver().clone();
    let before = runtime.currency().unwrap();
    let active: Vec<_> =
        (0..5).map(|_| original.client().try_acquire().unwrap().unwrap()).collect();
    assert!(!runtime.try_lend().unwrap(), "active tokens cannot fund lending");
    assert_eq!(runtime.budget().unwrap(), width(6));
    runtime.check_currency(&before).unwrap();
    for token in active {
        token.return_to_server().unwrap();
    }
    assert!(runtime.try_lend().unwrap());
    assert!(runtime.check_currency(&before).is_err());
    assert_eq!(runtime.budget().unwrap(), width(4));
    assert!(runtime.try_lend().unwrap());
    assert_eq!(runtime.budget().unwrap(), width(2));
    assert!(!runtime.try_lend().unwrap());
    assert_eq!(original.client().available().unwrap(), 1);
    // Same exact client sees explicit returns only after real reacquisition.
    assert!(runtime.try_reacquire_observed(Some(1 << 30)).unwrap());
    assert_eq!(runtime.budget().unwrap(), width(4));
    assert_eq!(original.client().available().unwrap(), 3);
    assert!(runtime.try_reacquire_observed(Some(1 << 30)).unwrap());
    assert_eq!(runtime.budget().unwrap(), width(6));
    assert_eq!(original.client().available().unwrap(), 5);
}

#[test]
fn runtime_reacquire_waits_for_original_queue_memory_and_real_competing_locks() {
    let root = tempfile::tempdir().unwrap();
    let native = tempfile::tempdir().unwrap();
    let mut runtime = fixture(root.path(), native.path());
    let original = runtime.jobserver().clone();
    assert!(runtime.try_lend().unwrap());
    assert!(runtime.try_lend().unwrap());
    let mut earlier = coordinator(root.path(), 3);
    assert!(matches!(
        earlier
            .ticket
            .attempt(
                Some(1 << 30),
                |_| Ok(true),
                |_, _| Ok(true),
                |_| Ok::<Option<()>, io::Error>(None)
            )
            .unwrap(),
        Attempt::Waiting(_)
    ));
    // A fit older request must not be bypassed by the resize owner.
    assert!(!runtime.try_reacquire_observed(Some(1 << 30)).unwrap());
    assert_eq!(runtime.budget().unwrap(), width(2));
    let competing = reserve(&mut earlier, 3).publish_fixed(width(8), width(6)).unwrap();
    assert!(!runtime.try_reacquire_observed(Some(1 << 30)).unwrap());
    assert_eq!(original.client().available().unwrap(), 1);
    drop(competing);
    assert!(!runtime.try_reacquire_observed(None).unwrap());
    assert!(!runtime.try_reacquire_observed(Some(0)).unwrap());
    assert!(runtime.try_reacquire_observed(Some(1 << 30)).unwrap());
    assert_eq!(original.client().available().unwrap(), 3);
}

#[test]
fn runtime_rejects_foreign_currency_and_drop_never_refunds_or_releases_exposed_claim() {
    let a = tempfile::tempdir().unwrap();
    let an = tempfile::tempdir().unwrap();
    let b = tempfile::tempdir().unwrap();
    let bn = tempfile::tempdir().unwrap();
    let mut runtime = fixture(a.path(), an.path());
    let other = fixture(b.path(), bn.path());
    assert!(runtime.check_currency(&other.currency().unwrap()).is_err());
    let original = runtime.jobserver().clone();
    assert!(runtime.try_lend().unwrap());
    let count = original.client().available().unwrap();
    drop(runtime);
    assert_eq!(original.client().available().unwrap(), count);
    let worktree =
        OpenOptions::new().read(true).write(true).open(a.path().join("worktree.lock")).unwrap();
    assert!(
        !try_exclusive(&worktree).unwrap(),
        "unknown exposed-owner drop retains actual worktree backing"
    );
}

#[test]
fn runtime_cannot_lend_the_original_explicit_minimum() {
    let root = tempfile::tempdir().unwrap();
    let native = tempfile::tempdir().unwrap();
    let pool = Pool::open_in(native.path(), width(8)).unwrap();
    let mut queue = coordinator(root.path(), 3);
    let claim = reserve(&mut queue, 3).publish_fixed(width(8), width(6)).unwrap();
    let mut runtime = RuntimeFixedClaim::new(claim, pool).unwrap();
    assert!(!runtime.try_lend().unwrap());
    assert_eq!(runtime.budget().unwrap(), width(6));
}
