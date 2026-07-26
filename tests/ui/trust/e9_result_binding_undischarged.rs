//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//! Falsification pair of `e9_result_binding_discharge`: the reflexivity (`>=`)
//! theorem must NOT discharge the STRICT `result > x` clause — the elaborated
//! goal `∀ x, identity_def(x) > x` is a different (and false) proposition.

clean {
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => Nat.le.refl (UInt64.toNat x)
}

pub fn identity(x: u64) -> u64
    //~^ ERROR Trust strict verification failed for
    ensures result > x by u64_ge_refl
    //~^ ERROR citation `u64_ge_refl`
{ x }

fn main() {}
