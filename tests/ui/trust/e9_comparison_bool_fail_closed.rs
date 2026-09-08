//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The NET under `e9_comparison_bool_discharge`. Widening `==` to a `Bool`
//! relation carrier must not widen anything else, so each citation here is one
//! step outside the new lane and each must stay refused with a reason that names
//! the real cause.
//!
//! * `unordered` — `bool` has no ORDER. A decided bool-valued side may be
//!   compared with `==` and nothing else. Were this admitted, the goal would be
//!   `Nat.le` applied to two `Bool`s and only the ill-typed-goal gate would stand
//!   between it and a discharge.
//! * `mixed` — a genuinely mixed comparison still reports a mixed comparison.
//!   The whole point of the change is that a NESTED comparison is no longer
//!   mistaken for one; a real one must still be caught.
//! * `not_bool_valued` — a call in proposition position is a proposition only
//!   when the callee's admission RECORDS a `Bool` return. `idn` is E6-admitted
//!   (the projection shape) and returns `i64`, so it keeps the unchanged E6
//!   fail-closed diagnostic. The gate is "records `Bool`", never "is admitted".

clean {
    def key64 (v : BitVec 64) : Nat :=
        Nat.xor (BitVec.toNat v) 9223372036854775808
    theorem key64_le_refl : forall (a : BitVec 64), Nat.le (key64 a) (key64 a) :=
        fun a => Nat.le.refl (key64 a)
}

pub fn unordered(a: i64, b: i64) -> bool
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    ensures result <= (a <= b) by key64_le_refl
    //~^ ERROR cannot be validated
{
    a <= b
}

pub fn mixed(a: i64, flag: bool) -> bool
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    ensures a == flag by key64_le_refl
    //~^ ERROR cannot be validated
{
    flag
}

pub fn idn(x: i64) -> i64 {
    x
}

pub fn not_bool_valued(x: i64) -> i64
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    ensures idn(x) by key64_le_refl
    //~^ ERROR cannot be validated
{
    x
}

fn main() {}
