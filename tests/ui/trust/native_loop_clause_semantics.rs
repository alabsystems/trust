//@ revisions: correct wrong_entry wrong_step wrong_decrease
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Cstrip=none
//@[correct] build-pass
//@[wrong_entry] check-fail
//@[wrong_step] check-fail
//@[wrong_decrease] check-fail
//@ dont-check-compiler-stderr
//! Source-to-verdict gate for first-class E4/E5 clauses. The correct revision
//! must discharge initiation, consecution, and strict decrease through the
//! ordinary verifier path. The negative revisions isolate initiation,
//! consecution, and strict-decrease failures so authored loop facts can never
//! be accepted as documentation or assumed merely because they were written.

#[cfg(correct)]
pub fn countdown(limit: u32) {
    let mut n = limit;
    while n > 0 invariant n <= limit decreases n {
        n -= 1;
    }
}

#[cfg(wrong_entry)]
pub fn fails_at_entry(mut n: u32) { //[wrong_entry]~ ERROR Trust strict verification failed for
    while n > 0 invariant n == 0 {
        n -= 1;
    }
}

#[cfg(wrong_step)]
pub fn fails_consecution() { //[wrong_step]~ ERROR Trust strict verification failed for
    let mut n = 0u32;
    while n < 2 invariant n == 0 {
        n += 1;
    }
}

#[cfg(wrong_decrease)]
pub fn fails_decrease(mut n: u32) //[wrong_decrease]~ ERROR Trust strict verification failed for
{
    while n > 0 invariant n >= 0 decreases 0 {
        n -= 1;
    }
}

fn main() {}
