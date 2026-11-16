//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (wave-UB2): a shared borrow of the UNIT value — `&u` on a
//! ground-truth-unit local and `&()` on the value-less unit rvalue — snapshots
//! the unit's one inhabitant, so `assert_eq!(.., ())` lowers. Under `strict`.

fn nothing() {}

fn unit_param(u: ()) {
    assert_eq!(u, ());
}

fn unit_call() {
    assert_eq!(nothing(), ());
}

fn main() {
    unit_param(());
    unit_call();
}
