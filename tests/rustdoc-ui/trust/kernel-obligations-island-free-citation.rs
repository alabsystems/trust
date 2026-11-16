// Trust (TG3, COMPILE-TIME-FACTS-1): a crate with no Clean island whose clause
// cites a theorem. Its compilation refuses the citation (cross-crate citation is
// not wired, and nothing local declares it); documenting it used to skip the
// kernel lane because the rustdoc gate looked only for islands. The gate now
// also reads `by` citations from HIR, so rustdoc refuses it too.
//
//@ compile-flags: -Ztrust-verify=off

pub fn ident(x: u64) -> u64
    ensures result == x by no_such_theorem
//~^ ERROR
{
    x
}
