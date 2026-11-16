use super::*;
use std::os::fd::AsRawFd;

#[test]
fn captive_initial_credits_require_backing_and_final_drain_never_restores_them() {
    let (fifo, mut escrow) = PrivateFifo::new_captive(4).unwrap();
    assert_eq!(fifo.available(), 0);
    assert!(fifo.try_escrow().unwrap().is_none());
    escrow.return_backed(2).unwrap();
    assert_eq!(fifo.available(), 2);
    let worker = fifo.jobserver.client().try_acquire().unwrap().unwrap();
    assert!(!escrow.try_recapture_backed(2).unwrap());
    assert_eq!(
        fifo.available(),
        1,
        "failed capture returns only actually backed credits"
    );
    assert_eq!(
        escrow.tokens.len(),
        1,
        "unfunded original credit stays captive"
    );
    drop(worker);
    assert!(escrow.try_recapture_backed(2).unwrap());
    assert_eq!(fifo.available(), 0);
    escrow.retire_drained().unwrap();
    assert_eq!(
        fifo.available(),
        0,
        "positive final drain permanently retires all credits"
    );
    let (single, escrow) = PrivateFifo::new_captive(1).unwrap();
    escrow.retire_drained().unwrap();
    assert_eq!(single.available(), 0);
}

#[test]
fn real_missing_token_defers_and_partial_acquisition_returns_to_original_fifo() {
    let fifo = PrivateFifo::fixture(4);
    let held = fifo.jobserver.client().try_acquire().unwrap().unwrap();
    assert_eq!(fifo.available(), 2);
    assert!(fifo.try_escrow().unwrap().is_none());
    assert_eq!(
        fifo.available(),
        2,
        "partial guards return; no replacement token is issued"
    );
    drop(held);
    let escrow = fifo.try_escrow().unwrap().unwrap();
    assert_eq!(fifo.available(), 0);
    assert!(
        fifo.try_escrow().unwrap().is_none(),
        "one original escrow owner"
    );
    let [read, write] = escrow.descriptors();
    assert_ne!(read.as_raw_fd(), write.as_raw_fd());
    for fd in [read, write] {
        let meta = std::fs::File::from(fd.try_clone_to_owned().unwrap())
            .metadata()
            .unwrap();
        assert_eq!(
            (meta.dev(), meta.ino()),
            (escrow.backing().device, escrow.backing().inode)
        );
        assert!(meta.file_type().is_fifo());
    }
    escrow.settled();
    assert_eq!(fifo.available(), 3);
    let guards: Vec<_> = (0..3)
        .map(|_| fifo.jobserver.client().try_acquire().unwrap().unwrap())
        .collect();
    assert!(fifo.jobserver.client().try_acquire().unwrap().is_none());
    drop(guards);
    assert_eq!(fifo.available(), 3);
}

#[test]
fn implicit_only_is_empty_and_unbound_extra_token_refuses_instead_of_changing_width() {
    let fifo = PrivateFifo::fixture(1);
    let escrow = fifo.try_escrow().unwrap().unwrap();
    assert_eq!(fifo.available(), 0);
    escrow.settled();
    // Test-only contamination is intentionally not inferred as admission or
    // silently consumed to manufacture a different foreign phase width.
    fifo.jobserver.client().release_raw().unwrap();
    assert!(fifo.try_escrow().is_err());
    assert_eq!(fifo.available(), 1);
}

#[test]
#[expect(
    clippy::disallowed_methods,
    reason = "isolated native abort actor selects its case before context/config"
)]
fn native_unknown_offer_exits_before_original_token_guards_can_return() {
    const ACTOR: &str = "TARGO_GNU_UNKNOWN_ACTOR";
    if let Some(parent) = std::env::var_os(ACTOR) {
        let directory = tempfile::tempdir_in(&parent).unwrap();
        let path = directory.path().join("credits");
        let fifo = Arc::new(PrivateFifo::in_directory(3, directory).unwrap());
        let mut escrow = fifo.try_escrow().unwrap().unwrap();
        assert_eq!(fifo.available(), 0);
        escrow.offered();
        std::fs::write(
            std::path::Path::new(&parent).join("checked-path"),
            path.as_os_str().as_bytes(),
        )
        .unwrap();
        drop(escrow);
        unreachable!("unknown offered escrow returned tokens");
    }
    let parent = tempfile::tempdir().unwrap();
    let module = module_path!().split_once("::").unwrap().1;
    let exact =
        format!("{module}::native_unknown_offer_exits_before_original_token_guards_can_return");
    let status = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", &exact])
        .env(ACTOR, parent.path())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .unwrap();
    assert_eq!(status.code(), Some(75));
    use std::os::unix::ffi::OsStringExt;
    let original = std::path::PathBuf::from(std::ffi::OsString::from_vec(
        std::fs::read(parent.path().join("checked-path")).unwrap(),
    ));
    let observed = Jobserver::from_fifo(&original).unwrap();
    assert_eq!(
        observed.client().available().unwrap(),
        0,
        "_exit happened before token release"
    );
}
