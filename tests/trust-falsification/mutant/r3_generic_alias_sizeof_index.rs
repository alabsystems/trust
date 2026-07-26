#![crate_type = "lib"]
// Trust R3 TRAP T1: `size_of::<T>()` feeding an index is LAYOUT-DEPENDENT —
// for T = [u64; 16] the index is 128 > 63 and this panics. The obligation
// must never be verified type-parametrically (a T-dependent term in the VC);
// it REFUTES (the size is unconstrained for-all-T). Must exit 1.
pub fn r3_t_sizeof<T>(xs: &[u8; 64]) -> u8 {
    xs[core::mem::size_of::<T>()]
}
