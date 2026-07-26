#![crate_type = "lib"]
// MUTANT of pending/proved/ffi_link_name_getuid.rs: the import is renamed to a
// decl name NO summary covers (`libc_getuid2` — still linking getuid, so it
// compiles and runs identically). The T9 alias binds by the EXACT decl name;
// it must NOT widen to prefix/fuzzy matching, so this call has no summary and
// must keep failing closed as "unmodeled FFI call: no summary, cannot prove
// safe" (exit 1). If this ever proves, name->summary binding grew a fuzzy
// matcher — an arbitrary foreign symbol could silently borrow a Safe contract
// (the exact false-PROVE channel the narrow alias was chosen to avoid).
unsafe extern "C" {
    #[link_name = "getuid"]
    fn libc_getuid2() -> u32;
}

/// Same call through the unmodeled alias name.
pub fn current_uid() -> u32 {
    // SAFETY: getuid() is always safe — no failure mode, no args.
    unsafe { libc_getuid2() }
}
