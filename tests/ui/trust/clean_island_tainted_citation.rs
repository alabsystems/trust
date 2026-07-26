//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! A rejected island can leave successfully registered siblings in the
//! crate-local environment. The session must be permanently tainted so no
//! later citation receives positive evidence from that partial state.

clean {
    theorem registered_before_failure : 0 = 0 := rfl
    theorem hole : True := sorry
    //~^ ERROR Clean island declaration `hole` uses explicit `sorry`
}

fn f() -> u32
    ensures 0 == 0 by registered_before_failure
    //~^ ERROR citation `registered_before_failure` cannot be validated because an earlier Clean island was rejected
{
    0
}

fn main() {
    let _ = f();
}
