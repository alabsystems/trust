//@ compile-flags: -Z trust-verify=off
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! E9 fail-closed boundary: source HIR names and primitive-looking types are
//! resolved into an exact per-clause mathematical statement domain. A matching
//! theorem is still advisory and cannot discharge the Rust/TrustIR VC until the
//! direct typed obligation and its SSA bindings are digest-bound end to end.

clean {
    theorem u64_refl : forall (x : UInt64), x = x := fun x => rfl
}

pub fn f_machine(x: u64, unused: bool) -> u64
    ensures result == result by u64_refl
    //~^ NOTE citation `u64_refl` has a Clean-kernel statement match
{
    x
}

type Word = u64;

pub fn f_subset(x: Word, unused_signed: i64, unused_flag: bool) -> Word
    requires x == x by u64_refl
    //~^ NOTE citation `u64_refl` has a Clean-kernel statement match
{
    let _ = (unused_signed, unused_flag);
    x
}

fn main() {
    let _ = f_machine(3, false);
    let _ = f_subset(4, -1, true);
}
