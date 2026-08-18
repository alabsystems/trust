//@ revisions: flipped built
//@ needs-trust-verify
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=on -Cstrip=none -Cdebuginfo=0
//@[built] compile-flags: -Ztrust-ir-flip=no
//@[flipped] check-fail
//@[built] check-fail
//@ dont-check-compiler-stderr
//! Regression for the measured E4 binder-erasure false proof. Before the
//! authenticated HIR-id -> MIR-place reconstruction landed, the flipped body
//! kept a named frozen argument and updated an anonymous loop temp. The
//! invariant below then bound the argument and incorrectly proved. Both
//! revisions must now refute the same consecution row; `flipped` additionally
//! exercises the TrustIR codegen lane while `built` is the semantic control.

pub fn frozen_entry_copy_must_not_prove(mut n: u32) //[flipped,built]~ ERROR Trust strict verification failed for
    requires n == 5
{
    while n > 0 invariant n == 5 {
        n -= 1;
    }
}

fn main() {}
