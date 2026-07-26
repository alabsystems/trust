//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//! Falsification pair of `e9_multi_clause_discharge`: with one clause UNCITED,
//! the conjunction is not proven and NOTHING discharges — both clauses'
//! obligations stay fail-closed build errors, including the one whose own
//! citation would have graded.

clean {
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => Nat.le.refl (UInt64.toNat x)
}

pub fn two(x: u64) -> u64
    //~^ ERROR Trust strict verification failed for
    ensures x >= x by u64_ge_refl
    ensures x <= x
{ x }

fn main() {}
