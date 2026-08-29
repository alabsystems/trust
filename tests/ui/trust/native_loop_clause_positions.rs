//@ revisions: correct wrong_entry wrong_step wrong_decrease
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Cstrip=none
//@[correct] build-pass
//@[wrong_entry] check-fail
//@[wrong_step] check-fail
//@[wrong_decrease] check-fail
//@ dont-check-compiler-stderr
//! Source-to-verdict gate for the E4/E5 clause position on `loop`.
//!
//! This is the sibling of `native_loop_clause_semantics.rs`, which covers
//! `while`. The two surfaces share ONE parser entry
//! (`parse_trust_loop_contract`) and ONE lowering
//! (`LoweringContext::collect_trust_loop_clauses`), so this file exists to
//! prove that sharing observationally: the same authored fact must be
//! discharged the same way, and the same false fact must fail the build on
//! either surface.
//!
//! Exit status alone would not be evidence — a clause that parsed and was then
//! dropped would also compile clean. `tests/run-make/trust-loop-clause-positions`
//! carries the obligation-level assertions; the negative revisions here are
//! what stop a dropped clause from passing this file.

#[cfg(correct)]
pub fn countdown(limit: u32) {
    let mut n = limit;
    loop invariant n <= limit decreases n {
        if n == 0 {
            break;
        }
        n -= 1;
    }
}

#[cfg(wrong_entry)]
pub fn fails_at_entry(mut n: u32) { //[wrong_entry]~ ERROR Trust strict verification failed for
    loop invariant n == 0 {
        if n == 0 {
            break;
        }
        n -= 1;
    }
}

#[cfg(wrong_step)]
pub fn fails_consecution() { //[wrong_step]~ ERROR Trust strict verification failed for
    let mut n = 0u32;
    loop invariant n == 0 {
        if n >= 2 {
            break;
        }
        n += 1;
    }
}

#[cfg(wrong_decrease)]
pub fn fails_decrease(mut n: u32) //[wrong_decrease]~ ERROR Trust strict verification failed for
{
    loop invariant n <= 100 decreases 0 {
        if n == 0 {
            break;
        }
        n -= 1;
    }
}

fn main() {}
