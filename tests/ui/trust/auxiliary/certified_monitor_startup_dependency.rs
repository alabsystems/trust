#![crate_type = "rlib"]
#![cfg_attr(startup_section, feature(used_with_arg))]

#[cfg(global_asm)]
core::arch::global_asm!("");

#[cfg(startup_section)]
extern "C" fn dependency_constructor() {}

#[cfg(startup_section)]
#[used(linker)]
#[cfg_attr(target_vendor = "apple", unsafe(link_section = "__DATA,__mod_init_func"))]
#[cfg_attr(target_os = "windows", unsafe(link_section = ".CRT$XCU"))]
#[cfg_attr(
    not(any(target_vendor = "apple", target_os = "windows")),
    unsafe(link_section = ".init_array")
)]
static DEPENDENCY_CONSTRUCTOR: extern "C" fn() = dependency_constructor;

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

pub fn ordinary_rust_symbol() {}
