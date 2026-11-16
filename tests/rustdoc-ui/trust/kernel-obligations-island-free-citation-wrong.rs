// Trust (TG16): documenting a crate checks its citations as compiling it does,
// whether or not the crate has a Clean island. TG3 ran rustdoc's kernel lane only for
// a crate with an island item, so a crate whose only kernel obligations were `by`
// citations documented with no diagnostic while `rustc -Ztrust-verify=off` refused
// the same file (tests/ui/trust/off_prelude_citation.rs is that compile). Both
// citations below are wrong and must be refused; `decreases` covers the clause kind
// beside `ensures` that the crate predicate reads.
//
//@ check-fail
//@ compile-flags: -Ztrust-verify=off

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
