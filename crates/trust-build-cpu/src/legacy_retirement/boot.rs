// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

//! Kernel-issued boot identity, never a caller-provided timestamp or PID.

use std::io;

use crate::invalid;

pub(super) fn current() -> io::Result<String> {
    #[cfg(target_os = "macos")]
    {
        let mut bytes = [0u8; 64];
        let mut count = bytes.len();
        // SAFETY: the literal is NUL-terminated, bytes/count are writable for
        // their declared lengths, and a null new-value requests read-only data.
        let result = unsafe {
            libc::sysctlbyname(
                c"kern.bootsessionuuid".as_ptr(),
                bytes.as_mut_ptr().cast(),
                &mut count,
                std::ptr::null_mut(),
                0,
            )
        };
        if result != 0 {
            return Err(io::Error::last_os_error());
        }
        if count == 0 || count > bytes.len() {
            return Err(invalid("invalid kernel boot identity size"));
        }
        // Each platform block is the function's tail once cfg removes the others.
        parse(
            std::str::from_utf8(&bytes[..count])
                .map_err(|_| invalid("kernel boot identity is not UTF-8"))?
                .trim_end_matches('\0'),
        )
    }
    #[cfg(target_os = "linux")]
    {
        use std::io::Read;
        let mut text = String::new();
        std::fs::File::open("/proc/sys/kernel/random/boot_id")?
            .take(65)
            .read_to_string(&mut text)?;
        parse(text.trim_end_matches('\n'))
    }
    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    Err(io::Error::new(io::ErrorKind::Unsupported, "kernel boot identity unavailable"))
}

pub(super) fn parse(value: &str) -> io::Result<String> {
    if value.len() != 36
        || !value.bytes().enumerate().all(|(index, byte)| {
            if [8, 13, 18, 23].contains(&index) { byte == b'-' } else { byte.is_ascii_hexdigit() }
        })
        || value.bytes().all(|byte| byte == b'0' || byte == b'-')
    {
        return Err(invalid("invalid kernel boot identity"));
    }
    Ok(value.to_ascii_lowercase())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn rejects_partial_caller_tokens_and_normalizes_kernel_uuid() {
        assert_eq!(
            parse("ABCDEF01-2345-6789-ABCD-0123456789AB").unwrap(),
            "abcdef01-2345-6789-abcd-0123456789ab"
        );
        for value in [
            "",
            "not-a-boot",
            "00000000-0000-0000-0000-000000000000",
            "abcdef01-2345-6789-abcd-0123456789ab extra",
        ] {
            assert!(parse(value).is_err());
        }
    }
    #[test]
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    fn native_boot_identity_is_stable() {
        assert_eq!(current().unwrap(), current().unwrap());
    }
}
