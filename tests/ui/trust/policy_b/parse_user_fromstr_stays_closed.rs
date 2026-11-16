//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Copt-level=0
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! The type-argument half of the vanilla-sysroot rule. `str::parse` is a core
//! routine, but instantiated at a USER type it calls that type's `FromStr` — user
//! code that may panic (this one does, on an empty input). The callee is therefore
//! NOT vanilla, its absent-callee row stays a fail-closed assumption panic, and the
//! default lane refuses the program. A green here would be a false verify.
use std::str::FromStr;
struct U;
impl FromStr for U {
    type Err = ();
    fn from_str(s: &str) -> Result<U, ()> {
        if s.is_empty() { panic!("empty") }
        Ok(U)
    }
}
fn main() {
    let s: String = std::env::args().nth(1).unwrap_or_default();
    let _ = s.parse::<U>();
}
