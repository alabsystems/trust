use super::*;

#[cfg(unix)]
mod unix {
    use std::os::unix::fs::{PermissionsExt, symlink};
    use std::sync::atomic::{AtomicU64, Ordering};

    use super::*;

    struct Directory(PathBuf);
    impl Directory {
        fn new() -> Self {
            static NEXT: AtomicU64 = AtomicU64::new(0);
            let base = PathBuf::from(std::env::var_os("HOME").expect("private home"))
                .join(".cache/trust-file-lock-tests");
            std::fs::create_dir_all(&base).unwrap();
            std::fs::set_permissions(&base, std::fs::Permissions::from_mode(0o700)).unwrap();
            let path = base.join(format!(
                "{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            std::fs::create_dir(&path).unwrap();
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o700)).unwrap();
            Self(path)
        }
    }
    impl Drop for Directory {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn exclusive_work_ownership_is_released_on_drop() {
        let root = Directory::new();
        let path = root.0.join("work");
        let first = try_exclusive_work_lock(&path).unwrap().unwrap();
        first.validate().unwrap();
        assert!(try_exclusive_work_lock(&path).unwrap().is_none());
        assert!(try_exclusive_work_lock(&root.0.join("other")).unwrap().is_some());
        drop(first);
        assert!(try_exclusive_work_lock(&path).unwrap().is_some());
    }

    #[test]
    fn replaced_sentinel_never_authorizes_publication() {
        let root = Directory::new();
        let path = root.0.join("work");
        let first = try_exclusive_work_lock(&path).unwrap().unwrap();
        std::fs::remove_file(lock_path_for(&path)).unwrap();
        let replacement = try_exclusive_work_lock(&path).unwrap().unwrap();
        assert!(first.validate().is_err());
        replacement.validate().unwrap();
    }

    #[test]
    fn unsafe_paths_and_sentinel_aliases_are_refused() {
        let root = Directory::new();
        assert!(try_exclusive_work_lock(Path::new("relative")).is_err());
        let alias = root.0.join("alias");
        symlink(&root.0, &alias).unwrap();
        assert!(try_exclusive_work_lock(&alias.join("work")).is_err());
        let victim = root.0.join("victim");
        std::fs::write(&victim, b"untouched").unwrap();
        let path = root.0.join("work");
        symlink(&victim, lock_path_for(&path)).unwrap();
        assert!(try_exclusive_work_lock(&path).is_err());
        assert_eq!(std::fs::read(&victim).unwrap(), b"untouched");
        std::fs::remove_file(lock_path_for(&path)).unwrap();
        std::fs::set_permissions(&victim, std::fs::Permissions::from_mode(0o600)).unwrap();
        std::fs::hard_link(&victim, lock_path_for(&path)).unwrap();
        assert!(try_exclusive_work_lock(&path).is_err());
    }

    #[test]
    fn contention_obeys_one_absolute_deadline() {
        let root = Directory::new();
        let path = root.0.join("work");
        let held = try_exclusive_work_lock(&path).unwrap().unwrap();
        let deadline = LockDeadline::new(Duration::from_millis(30));
        let result = FileLock::acquire_with_domain_check(&path, deadline, |_| Ok(()));
        assert!(matches!(result, Err(AuthorityError::Deadline { .. })));
        drop(held);
        assert!(try_exclusive_work_lock(&path).unwrap().is_some());
    }

    #[test]
    fn rejected_adoption_cannot_stamp_a_namespace() {
        let root = Directory::new();
        let path = root.0.join("state");
        let mut lock =
            FileLock::acquire_with_domain_check(&path, LockDeadline::new(Duration::ZERO), |_| {
                Ok(())
            })
            .unwrap();
        // Exercise the Linux marker state machine on every Unix host using
        // the same filesystem and lock implementation as production.
        lock.file.set_len(0).unwrap();
        let expected = "trust-memory-jobserver-lock-v1 pidns=1:2\n".to_owned();
        let result = lock.validate_domain_marker(&path, expected.clone(), |_| {
            Err(authority_error("live state cannot be adopted"))
        });
        assert!(matches!(result, Err(AuthorityError::Invalid(_))));
        assert_eq!(std::fs::metadata(lock_path_for(&path)).unwrap().len(), 0);
        lock.validate_domain_marker(&path, expected.clone(), |_| Ok(())).unwrap();
        assert_eq!(std::fs::read_to_string(lock.path()).unwrap(), expected);
        lock.validate_domain_marker(&path, expected, |_| {
            panic!("a matching marker must not re-adopt state")
        })
        .unwrap();
        assert!(
            lock.validate_domain_marker(&path, "different namespace\n".into(), |_| Ok(())).is_err()
        );
    }
}

#[cfg(not(unix))]
#[test]
fn unsupported_platform_cannot_claim_file_ownership() {
    assert!(try_exclusive_work_lock(Path::new("work")).is_err());
}
