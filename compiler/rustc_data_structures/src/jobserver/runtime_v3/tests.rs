use trust_resource_controller::Memory;

use super::*;

fn identity(pid: u32, birth: u64) -> Identity {
    Identity { pid, birth, birth_kind: BirthKind::MacosWallMicroseconds }
}
fn observed() -> Context {
    Context {
        session: "s-abcd".into(),
        root_attempt: [1; 16],
        host: "fixture".into(),
        boot: "1".into(),
        original_root: identity(10, 100),
        subject: Subject::RegisteredMember { identity: identity(20, 200), attempt: [2; 16] },
        cpu: Cpu::CooperativeShared {
            ceiling: 4,
            native_manifest: FileIdentity { device: 1, inode: 2 },
        },
        memory: Memory {
            bytes: 4 << 30,
            namespace: [1; 16],
            marker: "1-2-3".into(),
            epoch: [2; 16],
            guard: FileIdentity { device: 1, inode: 3 },
        },
        sdk: None,
    }
}
#[test]
fn observed_role_checks_never_promote_root_fixed_or_reused_identity() {
    // Pure post-authentication role checks only. These data do not supply
    // authentication, SDK custody, a native domain or any CPU grant.
    let mut context = observed();
    let own = identity(20, 200);
    assert!(member(&context, own).is_ok());
    context.subject = Subject::Root { identity: own };
    assert!(member(&context, own).is_err());
    context = observed();
    context.cpu =
        Cpu::RetainedFixed { units: 4, native_manifest: FileIdentity { device: 1, inode: 2 } };
    assert!(member(&context, own).is_err());
    context = observed();
    assert!(member(&context, identity(21, 200)).is_err());
    assert!(member(&context, identity(20, 201)).is_err());
    let mut wrong_units = own;
    wrong_units.birth_kind = BirthKind::LinuxStartTicks;
    assert!(member(&context, wrong_units).is_err());
}
#[test]
fn explicit_worker_memory_settings_remain_positive_without_new_caps() {
    assert_eq!(positive(None, 2 << 30).unwrap().get(), 2 << 30);
    assert_eq!(positive(Some(OsStr::new("17179869184")), 1).unwrap().get(), 16 << 30);
    for value in ["0", "-1", "", "garbage", "18446744073709551616"] {
        assert!(positive(Some(OsStr::new(value)), 1).is_err());
    }
}
#[test]
fn scoped_continuation_survives_positive_downscale_without_new_credits() {
    use std::num::NonZeroU32;
    use std::os::unix::fs::PermissionsExt;

    use trust_build_cpu::{LegacyRetirement, Owner, Pool, SlotState};
    struct Fixture {
        root: tempfile::TempDir,
        legacy: std::path::PathBuf,
    }
    impl Drop for Fixture {
        fn drop(&mut self) {
            // Private no-execution fixture only: let TempDir remove its
            // permission barrier after every actual descriptor closes.
            let _ = std::fs::set_permissions(&self.legacy, std::fs::Permissions::from_mode(0o700));
            if let Ok(entries) = std::fs::read_dir(&self.legacy) {
                for entry in entries.flatten() {
                    let _ = std::fs::set_permissions(
                        entry.path(),
                        std::fs::Permissions::from_mode(0o600),
                    );
                }
            }
        }
    }
    let root = tempfile::tempdir().unwrap();
    let legacy = root.path().join("legacy");
    std::fs::create_dir(&legacy).unwrap();
    let fixture = Fixture { root, legacy };
    let retired = LegacyRetirement::retire(&fixture.legacy, 1).unwrap();
    let pool = Pool::open_in(fixture.root.path(), NonZeroU32::new(4).unwrap()).unwrap();
    let debt = ExternalDebt::activate(&pool, &retired).unwrap();
    let owner = Owner::current(None);
    let mut leases = Vec::new();
    for _ in 0..4 {
        leases.push(debt.try_acquire_native(owner, 4).unwrap().unwrap());
    }
    let held = || {
        pool.snapshot()
            .unwrap()
            .iter()
            .filter(|slot| matches!(slot, SlotState::Held { .. }))
            .count()
    };
    let primary = leases[0].try_clone().unwrap().into_file();
    assert_eq!(held(), 4);
    assert!(
        debt.try_acquire_observed(owner, |_| 2).unwrap().is_none(),
        "NEW extra must respect the soft downscale"
    );
    let adopted =
        debt.try_adopt_inherited(&primary, |_| continuation_limit(2, 4)).unwrap().unwrap();
    assert_eq!(held(), 4, "continuation must not create another credit");
    assert!(
        debt.try_adopt_inherited(&primary, |_| continuation_limit(0, 4)).unwrap().is_none(),
        "zero still pauses continuation"
    );
    drop(adopted);
    drop(leases);
    drop(primary);
    assert_eq!(held(), 0);
    // Scoped primitive test only: no canonical NativeDomain, authenticated
    // Host/member, SDK context, machine activation or live work is claimed.
}
