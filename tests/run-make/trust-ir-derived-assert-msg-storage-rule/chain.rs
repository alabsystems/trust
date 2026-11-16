// Two real overflow-checked chains for rmake.rs. `chain2` has two checked adds: built retires the
// parameter's operand temp (`StorageDead`) in the block that ends in the SECOND overflow assert,
// whose message then reads a live `u64`. `chain1` has one checked add and retires nothing before
// its assert.

pub fn chain2(a: u64) -> u64 {
    a + 1 + 2
}

pub fn chain1(a: u64) -> u64 {
    a + 1
}
