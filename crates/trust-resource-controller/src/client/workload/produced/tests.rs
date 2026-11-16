use std::os::unix::fs::PermissionsExt;

use super::*;

#[test]
fn actual_original_descriptor_preflight_rejects_write_handles_and_aliases_without_reopening() {
    let parent = std::env::temp_dir();
    let mut nonce = [0u8; 16];
    // SAFETY: initialized bounded output for this native fixture name.
    assert_eq!(unsafe { libc::getentropy(nonce.as_mut_ptr().cast(), nonce.len()) }, 0);
    let name: String = nonce.iter().map(|byte| format!("{byte:02x}")).collect();
    let directory = parent.join(format!("trust-produced-fd-{name}"));
    std::fs::create_dir(&directory).unwrap();
    struct Cleanup(std::path::PathBuf);
    impl Drop for Cleanup {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
    let _cleanup = Cleanup(directory.clone());
    let path = directory.join("actual-output");
    std::fs::write(&path, b"actual original bytes").unwrap();
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o555)).unwrap();
    let held = File::open(&path).unwrap();
    let observed = executable(held.as_fd()).unwrap();
    use std::os::unix::fs::MetadataExt;
    let meta = held.metadata().unwrap();
    assert_eq!(
        observed,
        (crate::FileIdentity { device: meta.dev(), inode: meta.ino() }, meta.len())
    );
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();
    let writable = std::fs::OpenOptions::new().read(true).write(true).open(&path).unwrap();
    assert!(executable(writable.as_fd()).is_err());
    std::fs::hard_link(&path, directory.join("alias")).unwrap();
    assert!(executable(held.as_fd()).is_err());
    std::fs::remove_file(directory.join("alias")).unwrap();
    // The original FD remains observable even when its path is renamed. The
    // actual HeldProducedProgram/host root, not this preflight, must reject
    // namespace drift. No unsafe registration or native host is fabricated.
    std::fs::rename(&path, directory.join("original")).unwrap();
    std::fs::write(&path, b"replacement").unwrap();
    assert_eq!(executable(held.as_fd()).unwrap(), observed);
}
