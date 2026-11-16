//@ no-prefer-dynamic
//@ compile-flags: --crate-type=rlib --emit=metadata -Zalways-encode-mir -Ztrust-verify=off
//! A dependency compiled check-only, as `targo trust check` compiles every
//! library dependency: its encoded export list is empty. It exports a static
//! holding a function that spawns.

extern "C" fn dep_launch() {
    let _handle = std::thread::spawn(|| {});
}

#[unsafe(no_mangle)]
pub static TRUST_DEP_CHECK_ONLY_CALLBACK: extern "C" fn() = dep_launch;
