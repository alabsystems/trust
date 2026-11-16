//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//! nat-lift CLOSE NEGATIVE TWIN of `nat_lift_defeq_discharge.rs`, and the
//! mutation control for the one rejected design option that would have made the
//! lift unsound.
//!
//! The body WRAPS; the Lean definition does not. At `x = u64::MAX` the lifted
//! equation reads `0 = 2^64`, so it is false and nothing discharges it — this
//! must stay a build error.
//!
//! Why it is a control, not just a negative. The rejected alternative was to
//! narrow the LEAN side instead (`UIntN.ofNat`), which would have made this
//! clause TRUE for every `x`, silently. `UInt64.toNat (UInt64.ofNat (2^64)) = 0`
//! is measured in `crates/trust-spec-elab/tests/nat_lift_probes.rs`, and the
//! lift table structurally cannot emit `ofNat` — pinned by
//! `the_lift_table_is_closed_and_exact`. If this fixture ever goes green, that
//! is what happened.
//!
//! THE PIN IS THE POINT. Without it this fixture would pass if `x.wrapping_add(1)`
//! were simply not E6-admissible — the clause would then be refused upstream and
//! the lift never reached. Measured 2026-09-18 on stage1 from this tree: the
//! refusal is "the two sides are not definitionally equal (Eq.refl does not
//! check)", i.e. the body IS imported, the lifted goal IS built, and the KERNEL
//! is what declines it.

clean {
    def succ_nat (n : Nat) : Nat := n + 1
}

fn succ(x: u64) -> u64
    ensures (result as nat) == succ_nat(x as nat)
    //~^ ERROR the two sides are not definitionally equal (Eq.refl does not check)
{
    x.wrapping_add(1)
}

fn main() {
    let _ = succ(3);
}
