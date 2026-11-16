//! Preflight observations only. These files are not Layout guards and cannot
//! satisfy unsafe retain_output_locks or construct RetainedOutputLocks.
use std::os::unix::fs::PermissionsExt;

use super::*;

#[test]
fn actual_descriptor_order_count_access_and_backing_match_the_complete_census() {
    let mut random = [0u8; 16];
    // SAFETY: write one initialized bounded fixture nonce.
    assert_eq!(unsafe { libc::getentropy(random.as_mut_ptr().cast(), random.len()) }, 0);
    let name: String = random.iter().map(|byte| format!("{byte:02x}")).collect();
    let root = std::env::temp_dir().join(format!("original-output-preflight-{name}"));
    std::fs::create_dir(&root).unwrap();
    struct Cleanup(std::path::PathBuf);
    impl Drop for Cleanup {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
    let _cleanup = Cleanup(root.clone());
    use std::os::unix::ffi::OsStrExt;
    let mut request = Request {
        key: output::Key { root_attempt: [1; 16], invocation_sha256: [2; 32], attempt: [3; 16] },
        output_root: root.as_os_str().as_bytes().to_vec(),
        locks: vec![],
    };
    let mut files = Vec::new();
    for name in [".cargo-lock", ".cargo-build-lock", ".cargo-artifact-lock"] {
        let path = root.join(name);
        let file = std::fs::OpenOptions::new()
            .create_new(true)
            .read(true)
            .write(true)
            .open(&path)
            .unwrap();
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o600)).unwrap();
        let metadata = file.metadata().unwrap();
        request.locks.push(output::Lock {
            path: path.as_os_str().as_bytes().to_vec(),
            backing: FileIdentity { device: metadata.dev(), inode: metadata.ino() },
        });
        files.push(file);
    }
    let descriptions = files.iter().map(AsFd::as_fd).collect::<Vec<_>>();
    originals(&request, &descriptions).unwrap();
    assert!(originals(&request, &descriptions[..2]).is_err());
    let mut reversed = descriptions.clone();
    reversed.swap(0, 1);
    assert!(originals(&request, &reversed).is_err());
    let readonly = File::open(root.join(".cargo-lock")).unwrap();
    let mut wrong_access = descriptions.clone();
    wrong_access[0] = readonly.as_fd();
    assert!(originals(&request, &wrong_access).is_err());
}
