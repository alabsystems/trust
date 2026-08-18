//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -O
//@ check-pass
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ normalize-stderr: "\n\n$" -> "\n"
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//@ normalize-stderr: "sha256:[0-9a-f]{64}" -> "sha256:$$DIGEST"
//@ normalize-stderr: "trust-mc@\d+\.\d+\.\d+" -> "trust-mc@$$ENGINE"
//! Release-mode identity pin for exact core wrapping calls outside the narrow
//! E6 import lane. Signed and pointer-sized add/sub remain available to the
//! full assertion-refutation model, while u128 remains a precise total
//! TrustIR operation even though the <=64-bit refutation model declines it.
//! If MIR inlining erases any of these authenticated call identities before
//! Trust verification, they become ordinary overflow-obligated arithmetic and
//! this strict `-O` fixture fails.
//!
//! RE-PIN 2026-08-15 — 1 proved -> 1 runtime-checked, caused by UPSTREAM commit
//! 983bc1a3b6 ("REMOVE the panic-freedom subsumption lane"), NOT by anything on
//! our side. The movement is strictly stronger (more conservative): the
//! compiler now REFUSES to credit a proof it used to credit. Nothing here was
//! refuted before and is unrefuted now, no error vanished, and no verdict was
//! upgraded — `-Ztrust-policy=certify` rejects this file today and accepted it
//! before, which is the fail-closed direction.
//!
//! MECHANISM. Each of these two functions lowers to exactly ONE compiler result
//! row: the synthesized `assertion:panic-freedom:0` aggregate (measured — the
//! sibling `trust_mc_default_function:0` is a default admission and returns
//! Unsupported, so it is never a counted row). `refute_full_assert_obligations`
//! still proves the assert's panic path unreachable and still re-points the
//! aggregate at the GROUNDED residual violation — the stderr note "was grounded
//! by the compiler" below is that lane firing, and it fires only while the
//! `wrapping_add`/`wrapping_sub` call identities survive `-O`, so this file
//! still pins exactly what it was written to pin. That rewrite deliberately
//! revokes the row's public binding, so the row's only remaining route to a
//! private authority is a Clean-kernel certificate over the grounded residual.
//! MEASURED (`trust_certify::certify_vc` driven directly, both the pre-merge
//! clean pin 4c61046822 and the current 6bdd47cf5f): the kernel DECLINES both
//! residuals. The measured shape is a FORMULA-level `Ite` whose branches are
//! themselves equations — `Ite(Lt(i32::MAX, Add(_4,-1)), Eq(_3, Add(_4,
//! -4294967297)), Ite(Lt(Add(_4,-1), i32::MIN), Eq(_3, Add(_4, 4294967295)),
//! Eq(_3, Add(_4,-1))))` — while `certify_vc`'s only `Ite` lane
//! (`ite_index_branch_values`, crates/trust-certify/src/lib.rs:6649) matches
//! `Eq(var, Ite(intlit, intlit))`, a TERM-level `Ite` over closed literals. The
//! formula-level shape cannot reach that lane at all, so the decline is
//! structural, not a budget or a near-miss. Before 983bc1a3b6 the row was
//! carried past the S4 gate by `ResultProofAuthority::WholeFunctionPanicFreedom
//! Subsumption`, minted here over a VACUOUSLY true premise conjunction (the
//! aggregate was the sole row, so `all()` ranged over the empty set) — exactly
//! the false-proof shape upstream 1ab7ee48f2 named and 983bc1a3b6 deleted.
//! Restoring the "1 proved" line therefore requires restoring a deleted false
//! proof, and must not be done.
//!
//! TO CLOSE HONESTLY (then re-pin back to "1 proved"): teach the Clean kernel a
//! certificate for the wrapping-`Ite` residual — a 3-way case split per `Ite`
//! into linear-Int contradictions — so the grounded row earns `KernelCertified`
//! on its own. That is upstream's own named follow-up in 983bc1a3b6. Do NOT
//! recover this by crediting the native trust-mc verdict: it is ChcValidity
//! (Chc/SmtBacked, not kernel-rechecked) and 983bc1a3b6 explicitly evaluated and
//! DECLINED that route for this aggregate.

#![crate_type = "lib"]

pub fn signed_literal_roundtrip(x: i32) {
    assert!(x.wrapping_add(1).wrapping_sub(1) == x);
}

pub fn usize_roundtrip(x: usize, n: usize) {
    assert!(x.wrapping_add(n).wrapping_sub(n) == x);
}

pub fn u128_wrapping_is_total(x: u128, y: u128) -> u128 {
    x.wrapping_add(y)
}
