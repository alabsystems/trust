//@ needs-trust-verify
//@ revisions: pass first_mismatch second_mismatch
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --test -Awarnings
//@[pass] run-pass
//@[first_mismatch] run-crash
//@[first_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[second_mismatch] run-crash
//@[second_mismatch] error-pattern: kernel-certified Trust monitor failed
//@ dont-check-compiler-stderr

//! Function-level E5 monitors snapshot the measure at entry and check the
//! recursive argument at every exact direct-self Call. The two negative
//! revisions independently falsify distinct call sites, so one monitored edge
//! cannot make the other pass vacuously.

#[inline(never)]
fn two_call_sites(n: u8, use_second: bool) -> u8
    decreases n
{
    if n == 0 {
        return 0;
    }
    if use_second {
        #[cfg(second_mismatch)]
        return two_call_sites(n, use_second);
        #[cfg(not(second_mismatch))]
        return two_call_sites(n - 1, use_second);
    }
    #[cfg(first_mismatch)]
    return two_call_sites(n, use_second);
    #[cfg(not(first_mismatch))]
    two_call_sites(n - 1, use_second)
}

#[test]
fn certified_recursion_measure_checks_every_call_edge() {
    assert_eq!(two_call_sites(4, false), 0);
    assert_eq!(two_call_sites(4, true), 0);
}
