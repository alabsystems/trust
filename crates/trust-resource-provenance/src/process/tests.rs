use std::time::Duration;

use super::*;

#[test]
fn native_identity_image_and_account_are_observed_without_environment_authority() {
    let me = read_identity(std::process::id()).unwrap();
    assert_eq!(read_identity(me.pid).unwrap(), me);
    assert_eq!(presence(me.pid), Presence::Present);
    assert!(me.birth != 0 && me.unique_id != 0);
    let path = std::env::current_exe().unwrap();
    let image = File::open(&path).unwrap();
    assert!(image_matches(me, &image, &path).unwrap());
    assert!(!image_matches(me, &image, Path::new("/different-cached-image")).unwrap());
    let mut foreign = me;
    foreign.birth ^= 1;
    assert!(image_matches(foreign, &image, &path).is_err());
    assert!(account_home().unwrap().is_absolute());
    let (host, boot) = host_boot().unwrap();
    assert!(!host.is_empty());
    assert_eq!(boot.len(), 32);
}

#[test]
fn native_connected_peer_matches_exact_process_and_exec_identity() {
    let (first, _second) = UnixStream::pair().unwrap();
    let me = read_identity(std::process::id()).unwrap();
    check_peer(&first, me).unwrap();
    let mut wrong = me;
    wrong.birth ^= 1;
    assert!(check_peer(&first, wrong).is_err());
    #[cfg(target_os = "macos")]
    {
        let mut wrong = me;
        wrong.exec_version ^= 1;
        assert!(check_peer(&first, wrong).is_err());
    }
}

struct Child(std::process::Child);
impl Drop for Child {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

#[test]
fn actual_owned_child_ancestry_is_bounded_and_reread() {
    let me = read_identity(std::process::id()).unwrap();
    let child = Child(std::process::Command::new("/bin/sleep").arg("10").spawn().unwrap());
    let descendant = read_identity(child.0.id()).unwrap();
    assert!(stable_ancestor(me, descendant, Instant::now() + Duration::from_secs(2)).unwrap());
    let mut foreign = me;
    foreign.birth ^= 1;
    assert!(
        !stable_ancestor(foreign, descendant, Instant::now() + Duration::from_secs(2)).unwrap()
    );
    assert!(stable_ancestor(me, descendant, Instant::now()).is_err());
}
