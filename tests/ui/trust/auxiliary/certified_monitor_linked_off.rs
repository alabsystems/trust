//@ compile-flags: --crate-type=lib -Ztrust-verify=off
//@ no-prefer-dynamic

pub fn guarded(x: u64) -> u64
    requires x == 0
{
    x
}
