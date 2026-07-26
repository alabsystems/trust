//@ revisions: correct wrong_decrease
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Cstrip=none
//@[correct] build-pass
//@[wrong_decrease] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! End-to-end E5 gate for first-class function-signature `decreases`.
//! The positive revision has two distinct recursive call sites so source
//! admission requires the exact fresh per-call-site bijection; both calls
//! strictly decrease the authored unsigned measure. The negative revision
//! keeps the same native surface but passes the entry measure unchanged, which
//! must remain a visible unproved termination obligation.

#[cfg(correct)]
pub fn two_calls(n: u32) //[correct]~ NOTE Trust verification: 4 proved
    decreases n
{
    if n > 0 {
        two_calls(n - 1);
        two_calls(n - 1);
    }
}

#[cfg(wrong_decrease)]
pub fn no_descent(n: u32) //[wrong_decrease]~ NOTE Trust verification: 0 proved, 1 failed, 0 unknown
//[wrong_decrease]~| NOTE [termination] FAILED
//[wrong_decrease]~| ERROR Trust strict verification failed for
    decreases n
{
    if n > 0 {
        no_descent(n);
    }
}

fn main() {}
