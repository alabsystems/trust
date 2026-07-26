//@ needs-trust-verify
//@ dont-check-compiler-stderr
//@ needs-asm-support
//@ no-prefer-dynamic
//@ revisions: global_allocator global_asm inline_asm link_section naked no_main no_mangle export_name test_runner rustc_main
//@ compile-flags: -Ztrust-verify=off -Ztrust-verify-session=startup-controls-ui
//@ compile-flags: -Ztrust-targo-test-monitor -Awarnings
//@ rustc-env:TRUST_TARGO_TEST_MONITOR_SESSION=startup-controls-ui
//@ check-fail
//[global_allocator]~? ERROR certified-monitor tests reject source-controlled runtime roles in the selected crate
//[global_asm]~? ERROR certified-monitor tests reject unauthenticated global assembly
//[inline_asm]~? ERROR certified-monitor tests reject inline assembly
//[link_section]~? ERROR certified-monitor tests reject #[link_section]
//[naked]~? ERROR certified-monitor tests reject #[naked]
//[no_main]~? ERROR certified-monitor tests reject #![no_main]
//[no_mangle]~? ERROR certified-monitor tests reject #[no_mangle]
//[export_name]~? ERROR certified-monitor tests reject #[export_name]
//@[test_runner] compile-flags: --test
//[test_runner]~? ERROR certified-monitor tests reject custom #![test_runner]
//@[rustc_main] compile-flags: --test
//[rustc_main]~? ERROR certified-monitor tests reject source #[rustc_main]

#![cfg_attr(no_main, no_main)]
#![cfg_attr(test_runner, feature(custom_test_frameworks))]
#![cfg_attr(test_runner, test_runner(crate::runner))]
#![cfg_attr(rustc_main, feature(rustc_attrs))]

#[cfg(global_allocator)]
struct ExitAllocator;

#[cfg(global_allocator)]
unsafe impl std::alloc::GlobalAlloc for ExitAllocator {
    unsafe fn alloc(&self, _: std::alloc::Layout) -> *mut u8 {
        std::process::exit(0)
    }

    unsafe fn dealloc(&self, _: *mut u8, _: std::alloc::Layout) {}
}

#[cfg(global_allocator)]
#[global_allocator]
static GLOBAL_ALLOCATOR: ExitAllocator = ExitAllocator;

#[cfg(global_asm)]
core::arch::global_asm!("");

#[cfg(inline_asm)]
fn machine_level_return_escape() {
    unsafe { core::arch::asm!("", options(nomem, nostack)) }
}

#[cfg(link_section)]
#[cfg_attr(target_vendor = "apple", unsafe(link_section = "__DATA,__trustmon"))]
#[cfg_attr(target_os = "windows", unsafe(link_section = ".trust$M"))]
#[cfg_attr(
    not(any(target_vendor = "apple", target_os = "windows")),
    unsafe(link_section = ".trust_unauthenticated_startup")
)]
static STARTUP_SECTION: [u8; 0] = [];

#[cfg(naked)]
#[unsafe(naked)]
pub unsafe extern "C" fn naked_entry() {
    core::arch::naked_asm!("");
}

#[cfg(no_mangle)]
#[unsafe(no_mangle)]
pub extern "C" fn source_named_symbol() {}

#[cfg(export_name)]
#[unsafe(export_name = "trust_source_named_symbol")]
pub extern "C" fn source_exported_symbol() {}

#[cfg(test_runner)]
#[test_case]
static CUSTOM_CASE: () = ();

#[cfg(test_runner)]
fn runner(_: &[&()]) {}

#[cfg(rustc_main)]
#[rustc_main]
fn source_entry_override() {}

#[cfg(not(any(test_runner, no_main, rustc_main)))]
fn main() {}
