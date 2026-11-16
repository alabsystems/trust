// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates
// A bounded transport witness, not proof authority or a compiler substitute.
use jobserver_utils::Jobserver;
use std::os::fd::AsRawFd as _;

fn quoted(value: &str) -> String {
    let mut out = String::from("\"");
    for c in value.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c < ' ' => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn refusal(mode: &str, reason: &str) -> ! {
    println!(
        "NATIVE_TARGO_CUSTODY {{\"mode\":{},\"child_exit\":75,\"reason\":{},\"compiler_started\":false,\"marker\":false}}",
        quoted(mode), quoted(reason)
    );
    std::process::exit(75)
}

fn main() {
    // No argument files, sidecars or threads are opened before this checked import.
    let mut args = std::env::args().skip(1);
    let mode = args.next().expect("declared witness mode");
    let compiler = args.next().expect("selected sibling compiler");
    assert!(args.next().is_none());
    if mode == "missing" || mode == "malformed" {
        // SAFETY: this process is single-threaded and has not called foreign code.
        // These negative inputs affect this mini child alone, not its owner.
        unsafe {
            for name in ["CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS", "CARGO_JOBSERVER_FDS", "CARGO_JOBSERVER_HANDOFF"] {
                std::env::remove_var(name);
            }
            if mode == "malformed" {
                std::env::set_var("CARGO_MAKEFLAGS", "--jobserver-auth=-1,-1");
            }
        }
    }
    // SAFETY: capture is the first descriptor-sensitive operation at startup.
    let imported = unsafe { Jobserver::from_env_with_handoff_checked() };
    match (mode.as_str(), imported) {
        ("missing", Ok(None)) => refusal(&mode, "checked-import-unavailable"),
        ("malformed", Err(_)) => refusal(&mode, "checked-import-error"),
        ("positive", Ok(Some(owner))) => {
            let descriptors = owner.pipe_descriptors().expect("actual pipe descriptors");
            let mut identity = Vec::new();
            for fd in descriptors {
                let mut value = std::mem::MaybeUninit::<libc::stat>::uninit();
                // SAFETY: fstat writes one initialized stat for a live borrowed fd.
                assert_eq!(unsafe { libc::fstat(fd.as_raw_fd(), value.as_mut_ptr()) }, 0);
                let value = unsafe { value.assume_init() };
                assert_eq!(value.st_mode & libc::S_IFMT, libc::S_IFIFO);
                identity.extend([value.st_dev as u64, value.st_ino as u64]);
            }
            let before = owner.client().available().expect("observe original pipe credits");
            assert_eq!(before, 0, "one implicit CPU must not create an extra pipe credit");
            // A plain spawn closes unrelated descriptors. The selected Targo owner
            // must keep its original-pipe recovery endpoint alive through this wait.
            let output = std::process::Command::new(&compiler)
                .args(["--print", "sysroot"])
                .output()
                .expect("plain selected-compiler child");
            let after = owner.client().available().expect("observe unchanged pipe credits");
            assert_eq!(after, before);
            let hex = |raw: &[u8]| raw.iter().map(|b| format!("{b:02x}")).collect::<String>();
            println!(
                "NATIVE_TARGO_CUSTODY {{\"kind\":\"native-run\",\"observed_pipe\":{:?},\"available_before\":{},\"available_after\":{},\"compiler_exit\":{},\"compiler_stdout_hex\":{},\"compiler_stderr_hex\":{},\"sysroot\":{},\"marker\":\"native-targo-custody-positive-v1\"}}",
                identity, before, after, output.status.code().expect("normal compiler exit"),
                quoted(&hex(&output.stdout)), quoted(&hex(&output.stderr)),
                quoted(std::str::from_utf8(&output.stdout).expect("UTF8 sysroot").trim())
            );
            assert!(output.status.success(), "actual compiler refused original scheduler transport");
        }
        _ => panic!("checked transport did not match declared witness mode"),
    }
}
