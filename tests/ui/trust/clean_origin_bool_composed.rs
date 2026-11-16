//@ needs-trust-verify
//@ run-pass
//@ revisions: unoptimized optimized
//@ [unoptimized] compile-flags: -Ztrust-verify=off -Copt-level=0
//@ [optimized] compile-flags: -Ztrust-verify=off -Copt-level=2
//@ dont-check-compiler-stderr

// Trust: these are actual Rust calls to the functions minted from Clean
// definitions. A kernel-checked declaration without an emitted Rust body
// cannot satisfy either CTFE or the runtime truth tables.
mod decision {
    clean {
        def may_release (reaped poll_ok exit_observed : Bool) : Bool :=
            reaped || (poll_ok && exit_observed)
        def negated (a b c : Bool) : Bool := not (a || (b && not c))
        def with_literal (a b : Bool) : Bool := a || (b && true)
    }
}

const EXIT_OBSERVED: bool = decision::may_release(false, true, true);
const EXIT_PENDING: bool = decision::may_release(false, true, false);
const POLL_FAILED: bool = decision::may_release(false, false, true);
const ALREADY_REAPED: bool = decision::may_release(true, false, false);

fn main() {
    assert!(EXIT_OBSERVED);
    assert!(!EXIT_PENDING);
    assert!(!POLL_FAILED);
    assert!(ALREADY_REAPED);

    // The expected values are a literal full truth table, rather than a
    // second implementation of the expression being compiled.
    for (reaped, poll_ok, exit_observed, expected) in [
        (false, false, false, false),
        (false, false, true, false),
        (false, true, false, false),
        (false, true, true, true),
        (true, false, false, true),
        (true, false, true, true),
        (true, true, false, true),
        (true, true, true, true),
    ] {
        assert_eq!(decision::may_release(reaped, poll_ok, exit_observed), expected);
    }

    for (a, b, c, expected) in [
        (false, false, false, true),
        (false, false, true, true),
        (false, true, false, false),
        (false, true, true, true),
        (true, false, false, false),
        (true, false, true, false),
        (true, true, false, false),
        (true, true, true, false),
    ] {
        assert_eq!(decision::negated(a, b, c), expected);
    }

    for (a, b, expected) in [
        (false, false, false),
        (false, true, true),
        (true, false, true),
        (true, true, true),
    ] {
        assert_eq!(decision::with_literal(a, b), expected);
    }
}
