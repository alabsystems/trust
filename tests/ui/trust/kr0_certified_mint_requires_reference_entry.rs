//@ revisions: entry withheld
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Ztrust-policy=certify -Cpanic=abort
//@[withheld] rustc-env:TRUST_KR0_WITHHOLD_REFERENCE=1
//@ check-pass
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! KR0 switch (proven-core plan increment 2): a `Certified` row is minted only
//! with the certificate Clean's fenced reference entry issued for its exact
//! payload (`trust_certify::reference_certificate_for`).
//!
//! `entry`: the shift row of `shift_inline` is refuted by the clean CIC kernel
//! and its closed form is accepted by the reference entry, so the row is
//! kernel-certified (the stderr's "of which 1 kernel-certified" note).
//!
//! `withheld` (the negative control, a payload with NO reference certificate,
//! as for an old row or a payload the entry refused):
//! `TRUST_KR0_WITHHOLD_REFERENCE` makes trust-certify register no certificate,
//! so the identical payload mints no `KernelCertified` authority and the note
//! is gone: the row is still proved, by the strict solver re-check rung below
//! the kernel rung (`SolverRevalidated`, `Trusted`), never `Certified`.
//! Measured on the stage 1 of this change: the two stderr files differ in
//! exactly that note.
//! The unit-level controls are `trust_verify::tests::
//! kernel_rung_refuses_a_payload_the_reference_entry_never_accepted` (a tampered
//! and an unseen payload) and `trust_certify::reference_mint::tests::
//! an_extended_only_judgment_gets_no_reference_certificate` (a judgment the
//! `Extended` kernel accepts over a structurally added constant).

pub fn shift_inline(x: u64, bit: u32) -> Option<u64> {
    if !(bit < 64) {
        return None;
    }
    Some(x >> bit)
}
