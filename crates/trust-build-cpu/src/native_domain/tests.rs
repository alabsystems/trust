use super::*;

struct Cleanup {
    temp: tempfile::TempDir,
    // Declared last, so it is released only after the directory is removed.
    _kernel: crate::tests::KernelFixture,
}
impl Cleanup {
    /// Lend the held kernel fixture to a spawning helper.
    #[cfg(target_os = "macos")]
    fn kernel(&self) -> &crate::tests::KernelFixture {
        &self._kernel
    }
}

#[test]
fn migration_observation_never_creates_or_publishes_a_domain() -> io::Result<()> {
    let (_temp, layout, _pool) = fixture()?;
    assert_eq!(NativeDomain::migration_status(&layout)?, NativeMigrationStatus::NotStarted);
    assert_eq!(
        NativeDomain::resume(layout.clone()).err().map(|error| error.kind()),
        Some(io::ErrorKind::WouldBlock)
    );
    assert!(!layout.new.exists());
    assert_eq!(
        NativeDomain::retire(layout.clone()).err().map(|error| error.kind()),
        Some(io::ErrorKind::WouldBlock)
    );
    let new = open_parent(&layout.new)?;
    let before = read_record(&new)?.ok_or_else(|| invalid("missing retirement"))?;
    assert_eq!(NativeDomain::migration_status(&layout)?, NativeMigrationStatus::AwaitingLaterBoot);
    assert_eq!(
        NativeDomain::resume(layout.clone()).err().map(|error| error.kind()),
        Some(io::ErrorKind::WouldBlock)
    );
    assert_eq!(read_record(&new)?, Some(before.clone()));
    assert!(!layout.new.join(DIRECTORY_NAME).exists());
    let mut prior = before;
    prior.boot = "abcdef01-2345-6789-abcd-0123456789ab".into();
    assert_ne!(prior.boot, crate::legacy_retirement::kernel_boot()?);
    write_record(&new, &prior)?;
    assert_eq!(NativeDomain::migration_status(&layout)?, NativeMigrationStatus::ReadyToResume);
    assert_eq!(read_record(&new)?, Some(prior));
    assert!(!layout.new.join(DIRECTORY_NAME).exists());
    Ok(())
}

impl Drop for Cleanup {
    fn drop(&mut self) {
        fn restore(path: &Path) {
            let Ok(meta) = fs::symlink_metadata(path) else { return };
            if meta.is_dir() {
                let _ = fs::set_permissions(path, Permissions::from_mode(0o700));
                if let Ok(entries) = fs::read_dir(path) {
                    for entry in entries.flatten() {
                        restore(&entry.path());
                    }
                }
            } else if meta.is_file() {
                let _ = fs::set_permissions(path, Permissions::from_mode(0o600));
            }
        }
        // These fixtures contain no launched work. Restore only our own
        // private test files so TempDir can remove the permission barriers.
        restore(self.temp.path());
    }
}

fn fixture() -> io::Result<(Cleanup, Layout, Pool)> {
    // These tests assert that a dropped lease frees its slot at once. A child
    // that another test spawns holds a copy of every descriptor of this
    // process, these leases included, until its exec. Spawning tests hold the
    // crate's kernel fixture, so hold it before the first descriptor opens.
    let fixture = crate::tests::kernel_fixture();
    let temp = crate::tests::private_tempdir();
    let old = temp.path().join("capacity");
    let pool = Pool::open_in(&old, NonZeroU32::new(2).ok_or_else(|| invalid("zero"))?)?;
    let legacy = temp.path().join("build-slot");
    crate::tests::private_dir(&legacy);
    let layout = Layout { old, new: temp.path().join("capacity-v3"), legacy };
    Ok((Cleanup { temp, _kernel: fixture }, layout, pool))
}

/// This account's name, from a child spawned under the fixture's hold.
#[cfg(target_os = "macos")]
fn account(_kernel: &crate::tests::KernelFixture) -> io::Result<String> {
    let user = std::process::Command::new("/usr/bin/id").arg("-un").output()?;
    assert!(user.status.success());
    Ok(String::from_utf8(user.stdout).map_err(|_| invalid("nonUTF8 account"))?.trim().to_owned())
}

/// Run chmod(1) under the fixture's hold.
#[cfg(target_os = "macos")]
fn chmod(_kernel: &crate::tests::KernelFixture, args: &[&str], path: &Path) -> io::Result<bool> {
    Ok(std::process::Command::new("/bin/chmod").args(args).arg(path).status()?.success())
}

#[test]
fn barrier_excludes_raw_native_and_same_boot_readiness() -> io::Result<()> {
    let (_temp, layout, _pool) = fixture()?;
    assert_eq!(
        NativeDomain::retire(layout.clone()).err().map(|e| e.kind()),
        Some(io::ErrorKind::WouldBlock)
    );
    assert_eq!(
        Pool::open_existing(&layout.old).err().map(|e| e.kind()),
        Some(io::ErrorKind::PermissionDenied)
    );
    assert_eq!(
        NativeDomain::open(layout.clone()).err().map(|e| e.kind()),
        Some(io::ErrorKind::WouldBlock)
    );
    assert_eq!(
        NativeDomain::retire(layout.clone()).err().map(|e| e.kind()),
        Some(io::ErrorKind::WouldBlock)
    );
    assert!(!layout.new.join(DIRECTORY_NAME).exists());
    Ok(())
}

#[test]
fn held_native_credit_blocks_barrier_without_publishing() -> io::Result<()> {
    let (_temp, layout, pool) = fixture()?;
    let lease =
        pool.try_acquire(crate::Owner::current(None))?.ok_or_else(|| invalid("no credit"))?;
    assert_eq!(
        NativeDomain::retire(layout.clone()).err().map(|e| e.kind()),
        Some(io::ErrorKind::WouldBlock)
    );
    let new = open_parent(&layout.new)?;
    assert!(read_record(&new)?.is_none());
    assert!(Pool::open_existing(&layout.old)?.is_some());
    drop(lease);
    assert_eq!(
        NativeDomain::retire(layout).err().map(|e| e.kind()),
        Some(io::ErrorKind::WouldBlock)
    );
    Ok(())
}

#[test]
fn prepared_resume_restamps_completed_boot_and_tampering_refuses() -> io::Result<()> {
    let (_temp, layout, _pool) = fixture()?;
    assert!(NativeDomain::retire(layout.clone()).is_err());
    let new = open_parent(&layout.new)?;
    let mut record = read_record(&new)?.ok_or_else(|| invalid("missing receipt"))?;
    let current = record.boot.clone();
    record.phase = 0;
    record.boot = "-".into();
    write_record(&new, &record)?;
    assert_eq!(
        NativeDomain::retire(layout.clone()).err().map(|e| e.kind()),
        Some(io::ErrorKind::WouldBlock)
    );
    let complete = read_record(&new)?.ok_or_else(|| invalid("missing committed"))?;
    assert_eq!(complete.phase, 1);
    assert_eq!(complete.boot, current);
    let path = layout.old_pool().join(slot_name(0));
    fs::set_permissions(&path, Permissions::from_mode(0o600))?;
    assert_eq!(
        NativeDomain::retire(layout).err().map(|e| e.kind()),
        Some(io::ErrorKind::InvalidData)
    );
    Ok(())
}

#[test]
fn receipt_is_bounded_strict_and_read_only_open_creates_nothing() -> io::Result<()> {
    let (_temp, layout, _pool) = fixture()?;
    assert_eq!(
        NativeDomain::open(layout.clone()).err().map(|e| e.kind()),
        Some(io::ErrorKind::NotFound)
    );
    assert!(!layout.new.exists());
    assert!(NativeDomain::retire(layout.clone()).is_err());
    let new = open_parent(&layout.new)?;
    let record = read_record(&new)?.ok_or_else(|| invalid("missing"))?;
    let text = record.encode();
    assert!(text.len() < 2048);
    assert_eq!(Record::parse(&text)?, record);
    for bad in [
        format!("{text}\n"),
        text.replace("trust-native-domain-v1", "trust-native-domain-v2"),
        text.replace(" 2 ", " 02 "),
    ] {
        assert!(Record::parse(&bad).is_err());
    }
    Ok(())
}

#[test]
fn later_boot_publication_binds_new_pool_and_refuses_missing_receipt() -> io::Result<()> {
    let (_temp, layout, _pool) = fixture()?;
    assert!(NativeDomain::retire(layout.clone()).is_err());
    let new = open_parent(&layout.new)?;
    let mut record = read_record(&new)?.ok_or_else(|| invalid("missing"))?;
    let legacy = LegacyRetirement::open(&layout.legacy)?;
    // Fixture-only model of two barrier receipts surviving an intervening
    // kernel boot. Production has no supplied-boot constructor or override.
    let previous = "abcdef01-2345-6789-abcd-0123456789ab";
    assert_ne!(record.boot, previous);
    let anchor = layout.legacy.with_file_name("build-slot.retired-v3").join("state");
    let bytes = fs::read_to_string(&anchor)?;
    fs::write(&anchor, bytes.replace(legacy.retired_boot_id(), previous))?;
    record.boot = previous.into();
    write_record(&new, &record)?;
    let ready = NativeDomain::retire(layout.clone())?;
    ready.validate()?;
    assert_eq!(ready.pool().slots().get(), 2);
    assert!(Pool::open_existing(&layout.old).is_err());
    let owner = crate::Owner::current(None);
    let one = NonZeroU32::MIN;
    assert!(ready.pool().try_acquire(owner).is_err());
    let worker = ready.debt().try_acquire_native(owner, 2)?.ok_or_else(|| invalid("worker"))?;
    let fixed = ready.debt().try_reserve(owner, one, 2)?.ok_or_else(|| invalid("fixed"))?;
    let reopened = NativeDomain::open(layout.clone())?;
    assert!(reopened.debt().try_acquire_native(owner, 2)?.is_none());
    assert!(reopened.debt().try_reserve(owner, one, 2)?.is_none());
    drop(fixed);
    assert_eq!(reopened.debt().reserved()?, 1);
    assert!(reopened.debt().try_acquire_native(owner, 2)?.is_none());
    drop(worker);
    assert!(reopened.debt().try_acquire_native(owner, 2)?.is_some());
    let mut unbound = ready.record.clone();
    unbound.debt_root = None;
    write_record(&new, &unbound)?;
    assert!(NativeDomain::open(layout.clone()).is_err());
    fs::remove_file(layout.new.join(STATE))?;
    assert!(NativeDomain::open(layout).is_err());
    Ok(())
}

#[test]
fn unbound_new_pool_is_never_adopted_after_publication_crash() -> io::Result<()> {
    let (_temp, layout, _pool) = fixture()?;
    assert!(NativeDomain::retire(layout.clone()).is_err());
    let new = open_parent(&layout.new)?;
    let mut record = read_record(&new)?.ok_or_else(|| invalid("missing"))?;
    let legacy = LegacyRetirement::open(&layout.legacy)?;
    let previous = "abcdef01-2345-6789-abcd-0123456789ab";
    assert_ne!(record.boot, previous);
    let anchor = layout.legacy.with_file_name("build-slot.retired-v3").join("state");
    let bytes = fs::read_to_string(&anchor)?;
    fs::write(&anchor, bytes.replace(legacy.retired_boot_id(), previous))?;
    record.boot = previous.into();
    write_record(&new, &record)?;
    let _unbound = Pool::open_in(&layout.new, NonZeroU32::new(2).ok_or_else(|| invalid("zero"))?)?;
    assert_eq!(
        NativeDomain::retire(layout.clone()).err().map(|e| e.kind()),
        Some(io::ErrorKind::InvalidData)
    );
    assert_eq!(read_record(&new)?.map(|r| r.phase), Some(1));
    assert!(NativeDomain::open(layout).is_err());
    Ok(())
}

#[cfg(target_os = "macos")]
#[test]
fn read_only_manifest_acl_revokes_native_domain() -> io::Result<()> {
    let (cleanup, layout, _pool) = fixture()?;
    assert!(NativeDomain::retire(layout.clone()).is_err());
    let new = open_parent(&layout.new)?;
    let mut record = read_record(&new)?.ok_or_else(|| invalid("missing"))?;
    let legacy = LegacyRetirement::open(&layout.legacy)?;
    let previous = "abcdef01-2345-6789-abcd-0123456789ab";
    assert_ne!(record.boot, previous);
    let anchor = layout.legacy.with_file_name("build-slot.retired-v3").join("state");
    let bytes = fs::read_to_string(&anchor)?;
    fs::write(&anchor, bytes.replace(legacy.retired_boot_id(), previous))?;
    record.boot = previous.into();
    write_record(&new, &record)?;
    let ready = NativeDomain::retire(layout.clone())?;
    let user = account(cleanup.kernel())?;
    let manifest = layout.old_pool().join("pool");
    let grant = format!("user:{user} allow read");
    assert!(chmod(cleanup.kernel(), &["+a", &grant], &manifest)?);
    let raw_read = File::open(&manifest);
    let raw_write = OpenOptions::new().read(true).write(true).open(&manifest);
    let validation = ready.validate();
    let lookup = NativeDomain::open(layout);
    let mode = fs::metadata(&manifest)?.mode() & 0o777;
    assert!(chmod(cleanup.kernel(), &["-N"], &manifest)?);
    assert_eq!(mode, 0);
    assert!(raw_read.is_ok());
    assert_eq!(raw_write.err().map(|e| e.kind()), Some(io::ErrorKind::PermissionDenied));
    assert_eq!(validation.err().map(|e| e.kind()), Some(io::ErrorKind::InvalidData));
    assert_eq!(lookup.err().map(|e| e.kind()), Some(io::ErrorKind::InvalidData));
    ready.validate()?;
    Ok(())
}
