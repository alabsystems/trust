// T5A soundness control: deleting the "::ffi::" name entry must NOT shrink
// genuine unsafe-call coverage — it must GROW it. `danger()` is a local
// `unsafe fn` whose name matches NOTHING in the UNSAFE_PATTERNS list (no ptr/
// transmute/unchecked/ffi token), so the pre-T5A name heuristic never saw it:
// the undocumented unsafe block below sailed through detection. The
// AUTHORITATIVE signal (`Terminator::Call::is_unsafe_sig`, from tcx.fn_sig
// safety) is true for this call, so the missing-SAFETY demand must fire —
// there is deliberately NO "SAFETY:" comment on the unsafe block. This file
// must REFUTE (exit 1). If it ever proves, the signature-safety signal was
// lost between extraction and unsafe-block detection (or the demand was
// silently dropped), and every arbitrarily-named local unsafe fn regresses to
// the old name-list blind spot.
#![crate_type = "lib"]

/// Callee contract: caller must ensure `x != 0` (documented but unverified —
/// the point is the SIGNATURE is unsafe, not what the body does).
///
/// # Safety
/// `x` must be nonzero.
pub unsafe fn danger(x: u32) -> u32 {
    x.wrapping_mul(3)
}

/// The injected bug: an unsafe-sig call with NO preceding SAFETY comment.
#[must_use]
pub fn call_without_safety_comment(x: u32) -> u32 {
    unsafe { danger(x) }
}
