//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! Islands form one source-ordered Clean file session. Namespace/open state
//! from an earlier island must be available to later islands and citations.

clean {
    namespace Shared
    theorem zero_eq : 0 = 0 := rfl
    end Shared
}

clean {
    open Shared
    theorem reused : 0 = 0 := zero_eq
}

fn f() -> u32
    ensures 0 == 0
        by reused
        //~^ NOTE citation `reused` kernel-discharges this postcondition statement
{
    0
}

fn main() {
    let _ = f();
}
