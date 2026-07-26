//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//@ check-fail
//@ dont-check-compiler-stderr
//! E9 fail-closed: a citation whose theorem does NOT prove the clause's
//! elaborated obligation is a kernel rejection and a hard build error —
//! drift has no fallback.

clean {
    theorem zero_eq_thm : 0 = 0 := rfl
}

pub fn f_bad(x: u32) -> u32
    ensures 0 <= 0 by zero_eq_thm
    //~^ ERROR citation `zero_eq_thm` failed the strict Clean statement/certification audit
{
    x
}

fn main() {
    let _ = f_bad(3);
}
