use super::*;
use std::num::NonZeroU32;
use trust_build_cpu::{Owner, Pool, SlotState};

fn held(pool: &Pool) -> usize {
    pool.snapshot()
        .unwrap()
        .iter()
        .filter(|slot| matches!(slot, SlotState::Held { .. }))
        .count()
}

#[test]
#[cfg(target_os = "macos")]
fn actual_unsupported_pipe_borrows_one_credit_and_no_more() {
    let dir = tempfile::tempdir().unwrap();
    let pool = Pool::open_in(dir.path(), NonZeroU32::new(2).unwrap()).unwrap();
    let lease = pool.try_acquire(Owner::current(None)).unwrap().unwrap();
    let original = super::super::resource_serial::jobserver().unwrap();
    assert_eq!(
        original.client().try_acquire().unwrap_err().kind(),
        io::ErrorKind::Unsupported
    );
    assert_eq!(original.client().available().unwrap(), 0);
    assert_eq!(held(&pool), 1);
    let (local, fifo) = scheduler(&original, Some(&lease)).unwrap();
    assert!(local.client().try_acquire().unwrap().is_none());
    assert_eq!(held(&pool), 1, "no new implicit global credit");
    assert_eq!(original.client().available().unwrap(), 0);
    let mut metadata = std::process::Command::new("not-executed");
    local.configure(&mut metadata);
    let flags = metadata
        .get_envs()
        .find_map(|(key, value)| (key == "CARGO_MAKEFLAGS").then_some(value).flatten())
        .unwrap()
        .to_str()
        .unwrap();
    let path = std::path::PathBuf::from(
        flags
            .split_whitespace()
            .find_map(|part| part.strip_prefix("--jobserver-auth=fifo:"))
            .unwrap(),
    );
    assert!(path.exists());
    drop(metadata);
    drop(local);
    drop(fifo);
    assert!(
        !path.exists(),
        "private namespace follows its retained owner"
    );
    assert_eq!(held(&pool), 1);
    drop(lease);
    assert_eq!(held(&pool), 0);
}

#[test]
#[cfg(target_os = "macos")]
fn actual_unsupported_pipe_without_borrowed_lease_still_refuses() {
    let inherited = super::super::resource_serial::jobserver().unwrap();
    let error = scheduler(&inherited, None).err().unwrap();
    assert_eq!(
        error.downcast_ref::<io::Error>().unwrap().kind(),
        io::ErrorKind::Unsupported
    );
    assert_eq!(inherited.client().available().unwrap(), 0);
}

#[test]
fn other_probe_errors_are_preserved_even_with_a_borrowed_credit() {
    let dir = tempfile::tempdir().unwrap();
    let pool = Pool::open_in(dir.path(), NonZeroU32::new(1).unwrap()).unwrap();
    let lease = pool.try_acquire(Owner::current(None)).unwrap().unwrap();
    for kind in [
        io::ErrorKind::PermissionDenied,
        io::ErrorKind::BrokenPipe,
        io::ErrorKind::InvalidData,
    ] {
        for borrowed in [None, Some(&lease)] {
            let error = match transport(Err(io::Error::new(kind, "original refusal")), borrowed) {
                Err(error) => error,
                Ok(_) => panic!("ordinary errors must refuse"),
            };
            assert_eq!(error.kind(), kind);
            assert_eq!(error.to_string(), "original refusal");
        }
    }
    assert_eq!(held(&pool), 1);
}
