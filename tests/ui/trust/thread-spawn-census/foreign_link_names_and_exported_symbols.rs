//@ revisions: spawning quiet
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[quiet] forbid-output:UnmodeledThreadSpawnEffect
//! Spawn census (P2 review, probes h4, h10): foreign symbols resolve by link
//! name (design §5.2, §5.4). Only std-internal runtime symbols and `panic_impl`
//! did, so a foreign declaration of a local `#[no_mangle]` spawner was opaque
//! and `fire_by_name` QUIET, though the linker binds the call to the spawner. A
//! declaration now resolves to the function the crate graph exports under its
//! link name (`#[link_name]`, else its own name): `fire_by_name` is S2. A
//! function exported by symbol can also reach Rust as a pointer foreign code
//! hands back (`probe_get_cb` returning the spawner's address), so it is a
//! member of its shape's FnPool: `call_cb`, which only calls a pointer it is
//! given, is INDIRECT. `quiet`: no row.

#![allow(dead_code)]

#[cfg(spawning)]
fn launch() { //[spawning]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

#[cfg(quiet)]
fn launch() {}

#[unsafe(no_mangle)]
pub extern "C" fn trust_census_probe_exported_spawner() { launch() } //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops

mod inner {
    unsafe extern "C" {
        #[link_name = "trust_census_probe_exported_spawner"]
        pub fn by_link_name();
    }
}

pub fn fire_by_name() { unsafe { inner::by_link_name() } } //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops

pub fn call_cb(cb: extern "C" fn()) { cb() } //[spawning]~ NOTE may spawn (indirect)
