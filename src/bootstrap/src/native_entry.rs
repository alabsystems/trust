//! Process-wide setup shared by the native Bootstrap and managed Targo entries.

/// Exclude group/other writes when creating Bootstrap outputs, while preserving
/// every permission the caller already excluded. Existing files are untouched.
///
/// Bootstrap's own daemon authenticity checks reject writable directory chains.
/// A permissive inherited mask must not make newly built sysroots fail those
/// checks, including when the maintained engine runs inside managed Targo.
///
/// # Safety
/// Call only at single-threaded native process entry or in an isolated post-fork
/// child before it creates files. On Unix this briefly sets the process-global
/// mask while reading its old value; no other mask change or concurrent file
/// creation may observe that interval.
pub unsafe fn clamp_creation_mask_at_entry() {
    #[cfg(unix)]
    // SAFETY: the caller guarantees no concurrent mask change or file creation.
    // Both operations are syscall-only and allocate no descriptors.
    unsafe {
        let previous = libc::umask(0o022);
        libc::umask(previous | 0o022);
    }
}

#[cfg(all(test, unix))]
// Trust: out-of-line unit tests, as tidy's `unit_tests` check requires.
mod tests;
