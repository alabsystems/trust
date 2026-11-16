//@ revisions: unopt opt
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=off
//@[opt] compile-flags: -O
//@ check-fail
//@ dont-require-annotations: NOTE
//! TG16: the compile twin of rustdoc-ui/trust/kernel-obligations-island-free-*.rs.
//! A crate with no Clean island still carries kernel obligations when a clause
//! cites a theorem, and every ordinary build discharges them: `le_self`'s
//! citation of a true prelude theorem is kernel-checked, and the two wrong
//! citations are hard errors. rustdoc must give the same three verdicts.

pub fn le_self(x: u64) -> u64
    ensures forall n: nat, n <= n by Nat.le_refl
    //~^ NOTE kernel-discharges this postcondition statement
{
    x
}

pub fn wrong_theorem(x: u64) -> u64
    ensures forall n: nat, n <= n by Nat.zero_le
    //~^ ERROR citation `Nat.zero_le` failed the strict Clean statement/certification audit
{
    x
}

pub fn cited_measure(n: u64) -> u64
    decreases n by Nat.le_refl
    //~^ ERROR citation `Nat.le_refl` on a `decreases` clause cannot be validated
{
    n
}

fn main() {
    let _ = (le_self(1), wrong_theorem(2), cited_measure(3));
}
