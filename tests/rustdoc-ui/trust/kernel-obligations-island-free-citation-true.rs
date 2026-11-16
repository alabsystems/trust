// Trust (TG16): the positive twin of kernel-obligations-island-free-citation-wrong.rs.
// A crate with no Clean island whose `ensures … by` cites a true prelude theorem
// documents cleanly, and the kernel check says it ran: without this twin, a rustdoc
// lane that refused every citation would pass the negative test vacuously.
//
//@ check-pass
//@ compile-flags: -Ztrust-verify=off

pub fn le_self(x: u64) -> u64
    ensures forall n: nat, n <= n by Nat.le_refl
{
    x
}
