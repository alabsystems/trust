use std::os::unix::fs::MetadataExt as _;
use std::os::unix::process::CommandExt as _;
use std::process::Command;

#[test]
fn isolated_native_entries_preserve_stricter_masks_and_create_authentic_modes() {
    for (inherited, directory_mode, file_mode) in
        [(0o000, 0o755, 0o644), (0o002, 0o755, 0o644), (0o077, 0o700, 0o600), (0o277, 0o500, 0o400)]
    {
        let scratch = tempfile::tempdir().unwrap();
        let mut command = Command::new("/bin/sh");
        command.arg("-c").arg("mkdir directory && : > file").current_dir(scratch.path());
        // SAFETY: only the isolated post-fork child changes its mask. The
        // closure uses syscall-only operations before exec; the parallel
        // test runner's mask and its other children remain untouched.
        unsafe {
            command.pre_exec(move || {
                libc::umask(inherited);
                super::clamp_creation_mask_at_entry();
                Ok(())
            });
        }
        let output = command.output().unwrap();
        assert!(output.status.success(), "mask {inherited:o}: {output:?}");
        assert_eq!(
            scratch.path().join("directory").metadata().unwrap().mode() & 0o777,
            directory_mode,
            "inherited mask {inherited:o}",
        );
        assert_eq!(
            scratch.path().join("file").metadata().unwrap().mode() & 0o777,
            file_mode,
            "inherited mask {inherited:o}",
        );
    }
}
