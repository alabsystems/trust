//@ no-prefer-dynamic
//@ compile-flags: --crate-type=rlib --emit=metadata -Zalways-encode-mir -Ztrust-verify=off
//! A dependency compiled check-only, as `targo trust check` compiles every
//! library dependency: its encoded export list is empty. It exports a function
//! that spawns.

#[unsafe(no_mangle)]
pub extern "C" fn trust_dep_check_only_cb() {
    let _handle = std::thread::spawn(|| {});
}
