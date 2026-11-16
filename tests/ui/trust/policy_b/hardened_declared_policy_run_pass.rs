//@ needs-trust-verify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-profile=hardened -Zon-broken-pipe=error -Copt-level=0
//@ run-pass
//! The twin of hardened_generic_print_stays_mandated.rs with the policy DECLARED
//! explicitly: `-Zon-broken-pipe=error` keeps Rust's semantics (SIGPIPE ignored,
//! EPIPE -> `println!` panics, which is the `_print` row policy B reports) but it is
//! no longer ASSUMED, which is exactly what the mandate asks for. Discharged.
fn main() {
    println!("hello");
}
