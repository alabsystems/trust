//@ needs-trust-verify
//@ revisions: pass first_early_mismatch second_early_mismatch tail_mismatch
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --test -Awarnings
//@[pass] run-pass
//@[first_early_mismatch] run-crash
//@[first_early_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[second_early_mismatch] run-crash
//@[second_early_mismatch] error-pattern: kernel-certified Trust monitor failed
//@[tail_mismatch] run-crash
//@[tail_mismatch] error-pattern: kernel-certified Trust monitor failed
//@ dont-check-compiler-stderr
//! An executable `ensures` applies to every ordinary return from a function,
//! not only its lexical tail. The passing revision traverses both explicit
//! early returns and the tail path. Each crash revision then violates exactly
//! one path, so no return can silently bypass the certified monitor.

fn branchy_identity(x: u8) -> u8
    ensures result == x
{
    if x == 1 {
        #[cfg(first_early_mismatch)]
        return x + 1;
        #[cfg(not(first_early_mismatch))]
        return x;
    }

    if x == 2 {
        #[cfg(second_early_mismatch)]
        return x + 1;
        #[cfg(not(second_early_mismatch))]
        return x;
    }

    #[cfg(tail_mismatch)]
    {
        x + 1
    }
    #[cfg(not(tail_mismatch))]
    {
        x
    }
}

#[test]
fn certified_ensures_monitor_covers_every_ordinary_return() {
    #[cfg(pass)]
    {
        assert_eq!(branchy_identity(1), 1);
        assert_eq!(branchy_identity(2), 2);
        assert_eq!(branchy_identity(3), 3);
    }

    #[cfg(first_early_mismatch)]
    let _ = branchy_identity(1);
    #[cfg(second_early_mismatch)]
    let _ = branchy_identity(2);
    #[cfg(tail_mismatch)]
    let _ = branchy_identity(3);
}
