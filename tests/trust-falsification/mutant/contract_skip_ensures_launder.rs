#![crate_type = "lib"]
#![feature(contracts)]
#![feature(register_tool)]
#![register_tool(trust)]
#![allow(incomplete_features)]
// MUTANT (#5-PRE-B — never launder an UNPROVEN postcondition): `idx` carries an
// `#[ensures(*r < 8)]` that is FALSE for n >= 8, and `#[trust::skip]` means the
// callee is NEVER verified — its ensures is not proved. `caller` indexes
// `a[idx(n)]`; before #5-PRE-B the direct-call summary minted `idx`'s ensures as
// reusable evidence WITHOUT checking `idx` proved it, so the caller's L0 bounds
// VC discharged to PROVED by ASSUMING `idx() < 8` (a false PROVE), the build was
// GREEN under the default strict policy, and `caller([0;8], 8)` -> a[8] panicked at
// runtime. Trust must FAIL CLOSED: the mint is gated on `idx` actually proving
// its ensures (it did not — it was skipped), so the bounds VC is left unproved.
#[trust::skip]
#[core::contracts::ensures(move |r: &usize| *r < 8)]
pub fn idx(n: u64) -> usize {
    n as usize
}

#[core::contracts::requires(true)]
pub fn caller(a: [u8; 8], n: u64) -> u8 {
    a[idx(n)]
}
