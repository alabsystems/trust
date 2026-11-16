//@ needs-trust-verify
//@ revisions: plain_off plain_on optimized_off optimized_on
//@ run-pass
//@ compile-flags: -Ztrust-verify=off -Ztrust-policy=strict
//@ [plain_off] compile-flags: -Copt-level=0 -Ztrust-ir-lower=off
//@ [plain_on] compile-flags: -Copt-level=0 -Ztrust-ir-lower=on
//@ [optimized_off] compile-flags: -Copt-level=3 -Ztrust-ir-lower=off
//@ [optimized_on] compile-flags: -Copt-level=3 -Ztrust-ir-lower=on
//@ [plain_off] compile-flags: -Zmir-opt-level=0
//@ [plain_on] compile-flags: -Zmir-opt-level=0
//@ dont-check-compiler-stderr

// Trust: a read from an owned frame local remains pure. Disabling MIR
// optimization in the plain revision keeps the reference/copy/reborrow path
// visible instead of testing only a scalar body after reference elimination.
#![allow(dead_code)]

fn read(a: u64) -> u64 {
    let values = (a, 7u64);
    let first = &values.0;
    let copied = first;
    let reborrowed = &*copied;
    *reborrowed
}

clean {
    def applyRead (a : UInt64) : UInt64 := read a
}

fn main() {
    for a in [0, 1, 37, u64::MAX] {
        assert_eq!(applyRead(a), a);
    }
}
