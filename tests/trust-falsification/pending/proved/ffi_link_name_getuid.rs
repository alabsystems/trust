#![crate_type = "lib"]
// T9 (#[link_name] FFI summary alias — aterm-types dirs.rs shape): the import
// is declared under a RUST alias (`libc_getuid`) with the real symbol bound by
// `#[link_name = "getuid"]`. BUG (gate-logs-w3/aterm-types.log, dirs.rs:37):
// extraction drops the link_name attribute and keys the call on the decl path
// (`…::libc_getuid`), so the modeled `getuid` summary never bound and the call
// failed closed as "hardened boundary (ffi_boundary): libc_getuid: unmodeled
// FFI call: no summary, cannot prove safe" (UNKNOWN). FIX (narrow, honest):
// FfiSummaryDb registers the `libc_getuid` alias explicitly with getuid's
// contract (Safe, zero-arg, ret >= 0) — the general link_name-on-Call fix
// needs a new serialized Terminator field constructed in ~350 places.
// INTENT: MUST PROVE (exit 0) — the summary is Safe with no parameter
// demands, so no ffi_boundary VC survives.
//
// PENDING (not in the gate lanes yet): a foreign call still mints the
// absent-callee assumption row ("call to absent callee … may panic") that the
// in-flight absent-callee lane is being taught to route via summaries for
// `is_foreign` callees, and NO extern-"C"-calling fixture is currently green
// in proved/ (the hardened-FFI class sits in pending/, see
// mutant/extern_write_unbounded_fd.rs above). Promote this pair to the gate
// lanes once a summary-bound Safe foreign call verifies end-to-end; the alias
// MECHANISM is already pinned by the trust-vcgen unit test
// `test_libc_getuid_link_name_alias_binds_getuid_contract`.
unsafe extern "C" {
    #[link_name = "getuid"]
    fn libc_getuid() -> u32;
}

/// Effective-uid read via the aliased import.
pub fn current_uid() -> u32 {
    // SAFETY: getuid() is always safe — no failure mode, no args.
    unsafe { libc_getuid() }
}
