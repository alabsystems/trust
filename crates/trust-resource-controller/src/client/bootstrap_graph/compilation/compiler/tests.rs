//! No fake compiler/native Root or opaque-owner constructor fixtures.
use super::*;

#[test]
fn owner_deadline_anchors_at_rpc_start_and_observations_can_only_restrict() {
    let started = Instant::now();
    let initial = restrict(started, 60_000_000_000, None).unwrap();
    assert_eq!(initial, started + Duration::from_secs(60));
    let later = started + Duration::from_secs(10);
    assert_eq!(restrict(later, 60_000_000_000, Some(initial)).unwrap(), initial);
    assert_eq!(
        restrict(started, 30_000_000_000, Some(initial)).unwrap(),
        started + Duration::from_secs(30)
    );
    assert!(restrict(started, 0, Some(initial)).is_err());
    let expired = started - Duration::from_secs(1);
    assert!(restrict(later, 60_000_000_000, Some(expired)).is_err(), "expired owner cannot revive");
}
#[test]
fn compiler_adoption_requires_actual_own_process_birth_and_platform_identity() {
    let current = process::read_identity(std::process::id()).unwrap();
    let identity = Identity {
        pid: current.pid,
        birth: current.birth,
        birth_kind: if cfg!(target_os = "macos") {
            BirthKind::MacosWallMicroseconds
        } else {
            BirthKind::LinuxStartTicks
        },
    };
    own(identity).unwrap();
    assert!(own(Identity { pid: 1, ..identity }).is_err());
    assert!(own(Identity { birth: identity.birth + 1, ..identity }).is_err());
    let foreign = if cfg!(target_os = "macos") {
        BirthKind::LinuxStartTicks
    } else {
        BirthKind::MacosWallMicroseconds
    };
    assert!(own(Identity { birth_kind: foreign, ..identity }).is_err());
}
