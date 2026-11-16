//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! Trust (2026-09-26, std-absent-callee): `println!` under
//! `-Ztrust-policy=certify` — the designed outcome, stated in the refusal.
//!
//! `std::io::_print` DOES panic: `print_to` ends in
//! `panic!("failed printing to {label}: {e}")` whenever the write to stdout
//! returns an error (a full disk, EIO, EAGAIN on a non-blocking descriptor, EPIPE
//! while SIGPIPE is ignored). That depends on the process environment, not on any
//! value of the program, so no proof can exclude it, and `certify` — full static
//! discharge, no assumption rows — refuses the call BY DESIGN
//! (docs/design/trust-std-design.md, amendment 2026-09-26). The default policy
//! still reports it as a runtime-checked gap and builds
//! (`policy_b/println_default_run_pass.rs`); `policy_b/println_certify_rejects.rs`
//! pins the refusal itself.
//!
//! What THIS file pins is that the refusal says why: it names `_print`, the panic
//! site the sysroot panic census reached in std's own MIR, and why that panic cannot
//! be discharged. Before, `certify` printed the default policy's note ("keep the
//! call within that tolerated class"), which is no fix under `certify`.
fn main() {
    //~^ ERROR Trust strict verification failed
    //~| NOTE `std::io::stdio::_print` is a std/core/alloc function whose own MIR reaches panic sites that the sysroot panic census cannot exclude for every argument value: a call to `core::panicking::panic_fmt`, which does not return in `std::io::stdio::print_to`
    //~| NOTE this is std's stdout/stderr print backend
    //~| NOTE under `-Z trust-policy=certify` every unproved row is fatal
    println!("{}", 1u32);
}
