//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-pass
//@ dont-require-annotations: NOTE
//! E9: a result-free cited clause discharges on an ARBITRARY-body function.
//! `busy`'s body is no recognized kernel-import shape (multi-statement xor
//! chain) — but the clause never mentions `result`, so its kernel proof is a
//! ∀-params statement independent of the body, and the self-admission gate is
//! not required. The call inside the clause is still gated on ITS callee's
//! admission (`ident` kernel-imports). The paired negative shows the same body
//! with a RESULT-mentioning clause failing closed (no defining equation to
//! bind `result` to).
clean {
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => Nat.le.refl (UInt64.toNat x)
}
pub fn ident(x: u64) -> u64 { x }
pub fn busy(x: u64) -> u64
    ensures ident(x) >= ident(x) by u64_ge_refl
{
    let a = x ^ 3;
    let b = a ^ 3;
    b
}

fn main() {}
