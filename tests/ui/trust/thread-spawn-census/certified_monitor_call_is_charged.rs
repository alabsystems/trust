//@ revisions: monitored plain
//@ needs-trust-verify
//@[monitored] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --test
//@[plain] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[plain] forbid-output:certified_monitor_check
//! Spawn census (P2 review): in a monitored test session (`--test`, or Targo's
//! test marker) TrustVerify installs a kernel-certified runtime monitor in a
//! contract owner AFTER the census read its body: a call of
//! `core::contracts::certified_monitor_check`, which panics (nounwind) when the
//! clause fails, and the panic runs the panic hook. With a spawning hook, a
//! contract owner that cannot otherwise panic was QUIET. The census now charges
//! the monitor to every contract owner of a monitored session: `identity` is
//! INDIRECT under `monitored`; under `plain` no monitor is installed and no row
//! cites one.

#![allow(dead_code)]

fn launch() {
    let _handle = std::thread::spawn(|| {});
}

pub fn install() {
    std::panic::set_hook(Box::new(|_| launch()));
}

pub fn identity(flag: bool) -> bool //[monitored]~ NOTE may spawn (indirect)
    ensures result == flag
{
    flag
}
