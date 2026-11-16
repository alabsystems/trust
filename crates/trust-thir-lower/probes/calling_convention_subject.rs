//! Maintained original Rust input for the actual-owner direct-THIR ABI observer.
#![feature(rust_cold_cc, unboxed_closures, abi_swift, abi_vectorcall)]
#![allow(dead_code, improper_ctypes_definitions)]

pub fn rust_body(x: u64) -> u64 { x }
pub extern "C" fn c_body(x: u64) -> u64 { x }
pub extern "C-unwind" fn unwind_body(x: u64) -> u64 { x }
pub extern "system" fn system_body(x: u64) -> u64 { x }
pub extern "efiapi" fn efi_body(x: u64) -> u64 { x }
pub extern "rust-cold" fn cold_body(x: u64) -> u64 { x }
#[cfg(target_vendor = "apple")]
pub extern "Swift" fn swift_body(x: u64) -> u64 { x }
#[cfg(target_arch = "x86_64")]
pub extern "sysv64" fn sysv_body(x: u64) -> u64 { x }
#[cfg(target_arch = "x86_64")]
pub extern "win64" fn win_body(x: u64) -> u64 { x }
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub extern "vectorcall" fn vector_body(x: u64) -> u64 { x }
#[cfg(target_arch = "arm")]
pub extern "aapcs" fn aapcs_body(x: u64) -> u64 { x }

// Same result/one scalar input, but this source protocol requires tuple adaptation.
// The ordinary Fn/AssocFn path must decline it, never relabel it plain Rust.
pub extern "rust-call" fn tuple_protocol(x: (u64,)) -> u64 { x.0 }

unsafe extern "C" { fn foreign_c(x: u64) -> u64; fn foreign_variadic(x: u64, ...) -> u64; }
unsafe extern "C-unwind" { fn foreign_unwind(x: u64) -> u64; }
unsafe extern "system" { fn foreign_system(x: u64) -> u64; }
pub unsafe fn direct_c(x: u64) -> u64 { unsafe { foreign_c(x) } }
pub unsafe fn direct_unwind(x: u64) -> u64 { unsafe { foreign_unwind(x) } }
pub unsafe fn direct_system(x: u64) -> u64 { unsafe { foreign_system(x) } }

// RustCold has a distinct IR convention. Its bodyless declaration remains subject to
// the selected IR's foreign-layout rule even though unknown signatures refuse as Rust.
#[derive(Clone, Copy)]
pub struct RustLayout { pub lo: u64, pub hi: u64 }
unsafe extern "rust-cold" { fn foreign_cold_layout(x: RustLayout) -> RustLayout; }
pub unsafe fn direct_cold_layout(x: RustLayout) -> RustLayout {
    unsafe { foreign_cold_layout(x) }
}

pub fn indirect_rust(f: fn(u64) -> u64, x: u64) -> u64 { f(x) }
pub fn indirect_c(f: extern "C" fn(u64) -> u64, x: u64) -> u64 { f(x) }
pub fn indirect_unwind(f: extern "C-unwind" fn(u64) -> u64, x: u64) -> u64 { f(x) }
pub fn indirect_system(f: extern "system" fn(u64) -> u64, x: u64) -> u64 { f(x) }
pub fn indirect_cold(f: extern "rust-cold" fn(u64) -> u64, x: u64) -> u64 { f(x) }
pub fn indirect_tuple(f: extern "rust-call" fn((u64,)) -> u64, x: u64) -> u64 { f((x,)) }
pub fn closure_adapter(x: u64) -> u64 { let f: fn(u64) -> u64 = |a| a; f(x) }
