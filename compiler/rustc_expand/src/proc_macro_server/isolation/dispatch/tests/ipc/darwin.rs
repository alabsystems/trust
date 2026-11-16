//! Darwin restriction experiment in an owned fixture child, not macro admission.
//! The caller supplies an independently hash-checked read-only image. This does
//! not authenticate the worker/runtime, close ambient FDs or establish limits.

use std::io;

pub(super) fn restrict_readonly_fixture() -> trust_exec_policy::RestrictedNativeImage {
    let path = std::fs::canonicalize(std::env::var_os(super::DSO_PATH).unwrap()).unwrap();
    let image = std::fs::File::open(path).unwrap();
    assert!(!std::fs::read("/etc/hosts").unwrap().is_empty());
    let root = super::darwin_private_tmpdir(
        &std::env::var_os("TMPDIR").expect("forwarded private TMPDIR"),
    );
    assert_eq!(std::env::temp_dir(), root, "pre-restriction probe ignored private TMPDIR");
    let temporary = root.join(".ubd");
    let scratch = temporary.join(format!("trust-macro-policy-{}", std::process::id()));
    std::fs::write(&scratch, b"pre-restriction control").unwrap();
    std::fs::remove_file(&scratch).unwrap();
    let image = trust_exec_policy::restrict_current_to_readonly_image(image).unwrap();
    denied(std::fs::read("/etc/hosts").unwrap_err());
    denied(std::fs::write(&scratch, b"must not appear").unwrap_err());
    // SAFETY: this is a new owned socket, closed locally on every returned path.
    let socket = unsafe { libc::socket(libc::AF_INET, libc::SOCK_STREAM, 0) };
    if socket < 0 {
        denied(io::Error::last_os_error());
    } else {
        let address = libc::sockaddr_in {
            sin_len: std::mem::size_of::<libc::sockaddr_in>() as u8,
            sin_family: libc::AF_INET as u8,
            sin_port: 9_u16.to_be(),
            sin_addr: libc::in_addr { s_addr: u32::from_ne_bytes([127, 0, 0, 1]) },
            sin_zero: [0; 8],
        };
        // A local non-service endpoint; ECONNREFUSED is not policy denial.
        let result = unsafe {
            libc::connect(
                socket,
                (&raw const address).cast(),
                std::mem::size_of_val(&address) as libc::socklen_t,
            )
        };
        let error = io::Error::last_os_error();
        unsafe { libc::close(socket) };
        assert_eq!(result, -1);
        denied(error);
    }
    // SAFETY: an unexpectedly permitted child calls only _exit. The parent
    // retains and reaps that exact child before reporting a failed restriction.
    let child = unsafe { libc::fork() };
    if child == 0 {
        unsafe { libc::_exit(99) };
    }
    if child > 0 {
        let mut status = 0;
        loop {
            let result = unsafe { libc::waitpid(child, &mut status, 0) };
            if result == child {
                break;
            }
            assert!(result < 0 && io::Error::last_os_error().kind() == io::ErrorKind::Interrupted);
        }
        panic!("fixed restriction allowed fork");
    }
    denied(io::Error::last_os_error());
    let arguments = [c"true".as_ptr(), std::ptr::null()];
    // SAFETY: static argv. Any unexpected exec replaces only this owned child,
    // preventing Finish and failing the parent's normal lifecycle checks.
    assert_eq!(unsafe { libc::execv(c"/usr/bin/true".as_ptr(), arguments.as_ptr()) }, -1);
    denied(io::Error::last_os_error());
    eprintln!(
        "Darwin fixed deny-default: file read/write, network, fork and exec refused before DSO load"
    );
    image
}

fn denied(error: io::Error) {
    assert!(
        matches!(error.raw_os_error(), Some(libc::EPERM | libc::EACCES)),
        "expected policy denial, got {error}"
    );
}
