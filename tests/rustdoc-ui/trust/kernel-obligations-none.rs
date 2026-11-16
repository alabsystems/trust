// Trust (TG16): the cost and compatibility control for rustdoc's kernel lane. A crate
// with neither a Clean island nor a citation keeps upstream rustdoc's behavior:
// rustdoc does not type-check function bodies, so the ill-typed body below documents
// without an error. A lane that ran for every crate would type-check it through the
// contract query and report E0308 here (and charge every contract-heavy crate, std
// among them, for a check that has nothing to check).
//
//@ check-pass
//@ compile-flags: -Ztrust-verify=off

pub fn plain(x: u64) -> u64
    ensures result == x
{
    let _not_checked: u8 = "rustdoc does not type-check bodies";
    x
}
