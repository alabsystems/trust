//! Native CPU worker process identity is implemented on Linux and macOS only.

pub(crate) fn native_worker_host(os: &str) -> bool {
    matches!(os, "linux" | "macos")
}

#[cfg(test)]
mod tests {
    #[test]
    fn unsupported_hosts_cannot_select_native_workers() {
        for host in ["linux", "macos"] {
            assert!(super::native_worker_host(host));
        }
        for host in [
            "freebsd", "openbsd", "netbsd", "illumos", "windows", "unknown",
        ] {
            assert!(!super::native_worker_host(host));
        }
    }
}
