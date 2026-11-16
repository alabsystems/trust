//@ needs-trust-verify
//@ needs-asm-support
//@ edition: 2021
//@ revisions: asm_malloc asm_ctor asm_empty asm_certify section_ctor_data section_ctor_fn
//@ revisions: section_fn section_custom advisory island control
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[asm_certify] compile-flags: -Ztrust-policy=certify
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[asm_malloc] check-fail
//@[asm_ctor] check-fail
//@[asm_empty] check-fail
//@[asm_certify] check-fail
//@[section_ctor_data] check-fail
//@[section_ctor_fn] check-fail
//@[section_fn] check-fail
//@[section_custom] check-fail
//@[advisory] check-pass
//@[island] check-pass
//@[control] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
#![allow(dead_code)]
//! Trust (2026-10-01): CODE OR DATA THAT THE LINKER OR THE LOADER ACTS ON WITHOUT
//! A RUST CALL IS VERIFIED BY NO LANE
//! (`compiler/rustc_mir_transform/src/trust_verify/link_level_code.rs`;
//! docs/KNOWN_HAZARDS.md, "CLOSED 2026-10-01 — `global_asm!` and
//! `#[link_section]` ran unverified code without a Rust call").
//!
//! The witnesses, each measured on main `0.10.0+g07091c92c` as a library with a
//! driver built verify-off against the main-verified rlib (Mach-O spellings; the
//! assembly is never assembled by this check-only test):
//!
//! * `asm_malloc`: `global_asm!` DEFINES `_malloc`, returning `16`; `f` boxes a
//!   value, so std's `Global` allocator calls the assembly. rc=0 under the
//!   default policy and `certify` ("2 proved ... 1 skipped"), driver SIGSEGV
//!   (exit 139). The `#[no_mangle]` spelling of the same replacement is
//!   `symbol_interposition_refused.rs#malloc_box`.
//! * `asm_ctor`: `global_asm!` puts a pointer to a null-storing routine in
//!   `__mod_init_func`; the loader runs it before `main`. rc=0, SIGSEGV (139).
//! * `section_ctor_data`: a `#[used] #[link_section =
//!   "__DATA,__mod_init_func,mod_init_funcs"]` static whose value is a reference
//!   to DATA; the loader calls it. rc=0, SIGILL (132) before `main`.
//!
//! The rule refuses every non-island `global_asm!` and every `#[link_section]`
//! item, so the remaining check-fail revisions pin its COST, not a measured
//! crash: `asm_empty` (an empty template), `section_ctor_fn` (the `ctor` crate's
//! shape, a verified `extern "C" fn` in the constructor table),
//! `section_fn` (a function placed in the constructor table — its machine code
//! read as pointers) and `section_custom` (data in an inert custom section).
//! `asm_certify` is `asm_malloc` under `-Ztrust-policy=certify`.
//!
//! Controls: `advisory` keeps the explicit survey's contract (warnings, rc=0);
//! `island` is a `clean { … }` island, which shares `DefKind::GlobalAsm` but
//! lowers no machine code (also `r1/flip_with_island_present.rs`, build-pass);
//! `control` is a `#[used]` static and a C-ABI export with no section and no
//! assembly.
//!
//! BESIDE MAIN'S GRAPH-WIDE ALLOCATOR CHARGE (2026-10-08). Since 2026-10-04 main
//! counts a crate that holds non-island global assembly as a possible definer
//! of a libc allocator symbol (`SystemAllocatorInterposer::GlobalAsm`; its own
//! pins are `policy_b/system_allocator_symbol_from_global_asm.rs`), and charges
//! every body that can reach the allocator the refused
//! `contract:global-alloc-dealloc-panic-free` row. Both mechanisms are kept, and
//! `asm_malloc` / `asm_certify` draw both: this rule's error on the assembly
//! item, and main's row on `f`. Measured on main `0.10.0+gde6288ddd` with this
//! file: `asm_malloc` and `asm_certify` are refused there by that row;
//! `asm_ctor` (the measured SIGSEGV before `main`), `asm_empty` and the four
//! `section_*` revisions (`section_ctor_data` is the measured SIGILL) build
//! rc=0 there: no body of those crates reaches the allocator, and the charge
//! does not read `#[link_section]`. On that main this rule alone refuses them.

#[cfg(any(asm_malloc, asm_certify, advisory))]
std::arch::global_asm!(".globl _malloc", ".p2align 2", "_malloc:", "mov x0, #16", "ret");
//[asm_malloc,asm_certify]~^ ERROR Trust verification cannot accept global assembly
//[advisory]~^^ WARN Trust verification cannot accept global assembly

#[cfg(any(asm_malloc, asm_certify, advisory))]
pub fn f(x: u64) -> u64 {
    //[asm_malloc,asm_certify]~^ ERROR the `contract:global-alloc-dealloc-panic-free` caller contract is refused
    let b = Box::new(x);
    *b
}

#[cfg(asm_ctor)]
std::arch::global_asm!(
    //[asm_ctor]~^ ERROR Trust verification cannot accept global assembly
    ".section __DATA,__mod_init_func,mod_init_funcs",
    ".p2align 3",
    ".quad _trust_llc_ctor",
    ".text",
    ".p2align 2",
    "_trust_llc_ctor:",
    "mov x0, #0",
    "str x0, [x0]",
    "ret",
);

#[cfg(asm_empty)]
std::arch::global_asm!("");
//[asm_empty]~^ ERROR Trust verification cannot accept global assembly

#[cfg(any(asm_ctor, asm_empty))]
pub fn g(x: u64) -> u64 {
    x
}

#[cfg(any(section_ctor_data, advisory))]
#[used]
#[link_section = "__DATA,__mod_init_func,mod_init_funcs"]
static INIT: &[u8; 8] = &[0u8; 8];
//[section_ctor_data]~^ ERROR Trust verification cannot accept `#[link_section = "__DATA,__mod_init_func,mod_init_funcs"]` on `INIT`
//[advisory]~^^ WARN Trust verification cannot accept `#[link_section = "__DATA,__mod_init_func,mod_init_funcs"]` on `INIT`

#[cfg(section_ctor_fn)]
#[used]
#[link_section = "__DATA,__mod_init_func,mod_init_funcs"]
static CTOR: extern "C" fn() = early;
//[section_ctor_fn]~^ ERROR Trust verification cannot accept `#[link_section = "__DATA,__mod_init_func,mod_init_funcs"]` on `CTOR`

#[cfg(section_ctor_fn)]
extern "C" fn early() {}

#[cfg(section_fn)]
#[link_section = "__DATA,__mod_init_func,mod_init_funcs"]
pub fn placed(x: u64) -> u64 {
    //[section_fn]~^ ERROR Trust verification cannot accept `#[link_section = "__DATA,__mod_init_func,mod_init_funcs"]` on `placed`
    x
}

#[cfg(section_custom)]
#[link_section = "__DATA,__trust_llc"]
pub static TABLE: [u32; 4] = [1, 2, 3, 4];
//[section_custom]~^ ERROR Trust verification cannot accept `#[link_section = "__DATA,__trust_llc"]` on `TABLE`

#[cfg(island)]
clean {
    def trust_llc_island_ident (x : UInt64) : UInt64 := x
}

#[cfg(island)]
pub fn h(x: u64) -> u64 {
    x
}

#[cfg(control)]
#[used]
static KEEP: u32 = 7;

#[cfg(control)]
#[no_mangle]
pub extern "C" fn trust_llc_export(x: u32) -> u32 {
    x.wrapping_add(KEEP)
}
