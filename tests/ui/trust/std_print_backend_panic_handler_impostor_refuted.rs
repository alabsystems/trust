//@ needs-trust-verify
//@ aux-build: no_std_panic_handler_print_backend_impostor_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! THE PLANTED REFUTATION FOR THE RESIDENCY CONJUNCT OF `crate_is_authentic_std`
//! (trust_verify.rs), through its one consumer `def_is_std_print_backend`.
//!
//! The auxiliary crate's only sysroot-shaped anchor is the `#[panic_handler]`
//! every `#![no_std]` graph needs; in a graph that never loads `std` it OWNS the
//! `panic_impl` lang item. While `crate_is_authentic_std` decided identity by
//! that ownership alone, `def_is_std_print_backend` read the dependency's
//! panicking `io::_print` as std's own print backend, and
//! `fmt_writer_relative::body_formats_only_into_recognized_sinks` accepted it
//! as a std formatting sink for `P`'s writer-relative `Display`.
//!
//! The IMPOSTOR CALL stayed fail-closed either way (the masked-dispatch crate
//! rule, and the bridge keeps its row), so this is a belt, not a false proof.
//! What the unanchored predicate cost is the refusal's explanation: the
//! writer-relative sink note below was missing. MEASURED 2026-09-28 on stage-1
//! `trustc` at `52113eb46` (origin/main, before the fix): same two errors, no
//! note. A review mutant that dropped this conjunct and
//! `crate_is_authentic_core`'s (keeping `crate_is_authentic_foundational`'s)
//! passed all of tests/ui/trust, so this fixture is the conjunct's pin: a
//! mutant dropping those two and `def_is_alloc_fmt_format`'s failed exactly this
//! fixture and `fmt_writer_relative_string_lang_item_sink_impostor_refuted.rs`
//! (the missing note), measured 2026-09-28.
//!
//! Fix the compiler, not this file.
#![no_std]

extern crate no_std_panic_handler_print_backend_impostor_dep;

pub struct P;

impl core::fmt::Display for P {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("p")
    }
}

pub fn victim() {
    //~^ ERROR Trust Level 0 safety verification incomplete for `std_print_backend_panic_handler_impostor_refuted::victim`
    //~| ERROR Trust strict verification failed for `std_print_backend_panic_handler_impostor_refuted::victim`
    //~| NOTE this body hands its `fmt::Arguments` to a consumer that is not a std formatting sink
    no_std_panic_handler_print_backend_impostor_dep::io::_print(format_args!("{}", P));
}
