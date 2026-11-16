//! Trust (CUSTODY-BOUNDED-QUERY-SPELLINGS-1): in a strict fixed-width context
//! (`build-slot` protocol 1) that carries no GNU pool, the actual compiler
//! still answers each spelling of its fixed metadata queries: `-V` (Cargo's
//! `#[cargo_test]` asks it) and `--print sysroot` (toolchain discovery asks
//! it) as well as `--version` and `--print=sysroot`. Each is answered on no
//! scheduler. A producing invocation in the same context still refuses for
//! want of one, which shows the context is strict and the recognizer, not a
//! missing marker, admits them.

//@ ignore-windows the inherited-custody refusal is native Unix custody

use run_make_support::{CompletedProcess, cmd, rustc_path};

/// Every advertisement and custody locator a launcher could hand down.
const CUSTODY: [&str; 9] = [
    "CARGO_MAKEFLAGS",
    "MAKEFLAGS",
    "MFLAGS",
    "CARGO_JOBSERVER_HANDOFF",
    "TRUST_CPU_HANDOFF",
    "TRUST_CPU_IMPLICIT_FD",
    "ATERM_SDK_LEASE_V3",
    "ATERM_WORKLOAD_CPU_FDS_V1",
    "ATERM_WORKLOAD_HOST_STORE_FD_V1",
];

/// Run the actual compiler in a strict fixed-width context with no GNU pool.
fn strict_without_pool(args: &[&str], admitted: bool) -> CompletedProcess {
    let mut command = cmd(rustc_path());
    for name in CUSTODY {
        command.env_remove(name);
    }
    command.env("BUILD_SLOT_CPU_PROTOCOL", "1").args(args);
    if admitted { command.run() } else { command.run_fail() }
}

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    let version = strict_without_pool(&["--version"], true).stdout_utf8();
    assert!(!version.trim().is_empty());
    strict_without_pool(&["-V"], true).assert_stdout_equals(&version);
    strict_without_pool(&["-vV"], true).assert_stdout_contains(version.trim());
    let sysroot = strict_without_pool(&["--print=sysroot"], true).stdout_utf8();
    assert!(!sysroot.trim().is_empty());
    strict_without_pool(&["--print", "sysroot"], true).assert_stdout_equals(&sysroot);
    let targets = strict_without_pool(&["--print=target-list"], true).stdout_utf8();
    strict_without_pool(&["--print", "target-list"], true).assert_stdout_equals(&targets);

    // Positive control: the same context, a producing invocation.
    let refused = strict_without_pool(&["--crate-type=lib", "lib.rs"], false);
    assert_eq!(refused.status().code(), Some(75), "{refused:?}");
    refused.assert_stderr_contains("no captured inherited GNU scheduler");
    // A widened query is not a bounded query either.
    let widened = strict_without_pool(&["-V", "--crate-type=lib", "lib.rs"], false);
    assert_eq!(widened.status().code(), Some(75), "{widened:?}");
    // Nor is a bounded print beside an input, or beside another print.
    for args in [&["--print=sysroot", "lib.rs"][..], &["--print=sysroot", "--print=cfg"]] {
        let refused = strict_without_pool(args, false);
        assert_eq!(refused.status().code(), Some(75), "{args:?}: {refused:?}");
    }
}
