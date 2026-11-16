//@ revisions: extern_hook exported_static
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ compile-flags: -Ztrust-spawn-census-shadow=check
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output:violates its invariant
//! Spawn census, plan step P4 review (probes a07, a08; a linked C caller spawned a thread from
//! `run` in each): foreign code may call a callable it reads from memory it names by symbol, not
//! only one it is handed: an `extern` static a Rust frame stores a spawner into (`extern_hook`), or
//! a static the crate exports by symbol holding one (`exported_static`). The MIR lane (P2,
//! authoritative) charges both since 2026-10-03 (what Rust may store in memory foreign code reads
//! is handed to its foreign world), so `run`, which hands C nothing, is INDIRECT there. The
//! trust-ir lane says UNKNOWN: touching a global whose contents the module does not hold is a
//! hand-out (`foreign-callback`), an exported static a gap of the foreign world
//! (`exported-static`), and so is `c_launch`, a body with a foreign calling convention that
//! returns a value. No body here drops anything or calls std beyond the spawn seed.
//@[extern_hook] regex-error-pattern:(?m)^trust-spawn-census-shadow: body `register` mir=ESCAPES trust-ir=UNKNOWN trust-ir-unknown gaps=producer-declined$
//@[extern_hook] regex-error-pattern:(?m)^trust-spawn-census-shadow: body `run` mir=INDIRECT trust-ir=UNKNOWN trust-ir-unknown gaps=foreign-callback$
//@[exported_static] regex-error-pattern:(?m)^trust-spawn-census-shadow: body `run` mir=INDIRECT trust-ir=UNKNOWN trust-ir-unknown gaps=foreign-callback,exported-static$

#![allow(dead_code, improper_ctypes, improper_ctypes_definitions)]

pub fn launch() -> std::thread::JoinHandle<()> {
    std::thread::spawn(|| {})
}

pub extern "C" fn c_launch() -> std::thread::JoinHandle<()> {
    launch()
}

unsafe extern "C" {
    safe fn trust_p4_run();
    #[cfg(extern_hook)]
    static mut TRUST_P4_HOOK: extern "C" fn() -> std::thread::JoinHandle<()>;
}

#[cfg(extern_hook)]
pub fn register() {
    unsafe { TRUST_P4_HOOK = c_launch }
}

#[cfg(exported_static)]
#[unsafe(no_mangle)]
pub static TRUST_P4_CALLBACK: extern "C" fn() -> std::thread::JoinHandle<()> = c_launch;

pub fn run() {
    trust_p4_run()
}
