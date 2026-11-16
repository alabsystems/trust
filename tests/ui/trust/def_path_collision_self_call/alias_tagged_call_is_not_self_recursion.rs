//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: --crate-type lib -Ztrust-verify=on
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//! ARGS-FINGERPRINT-READ-1 round 3 (2026-10-07) — a call tagged `::<__trust_alias@…>` is
//! not a self call.
//!
//! The call below runs the GENERIC `get` (which loops forever for an even `x`) but prints
//! as the concrete `get`'s definition key, because the printer canonicalizes lifetimes
//! (SUMMARY-NAME-COLLIDE-1). The extractor therefore tags it `::<__trust_alias@…>` so no
//! lane matches it to the concrete body; but the termination lane's
//! `direct_call_identity` stripped that group as if it were a turbofish, and the call
//! read as a SELF call of the concrete `get`: a PROVED "recursion measure `x` may not
//! decrease" row. Round 3 keeps every verifier marker group as identity, and gates self
//! calls on the compiler's `DefId`-decided self-call blocks. MEASURED 2026-10-07 by hand
//! (`-Ztrust-verify=on`): preview3 stage 1 (main `7be75e9a80`) `2 proved, 0 failed,
//! 0 unknown, 0 timed out, 1 runtime-checked out of 3`; round-3 stage 1 the count below.

pub struct V<X>(pub X);
pub trait Marker {}
impl Marker for V<for<'a> fn(&'a u8) -> &'a u8> {}
pub struct W<T>(pub T);

impl<T: Marker> W<T> {
    pub fn get(x: u32) -> u32 {
        let mut k = x;
        while k != 7 {
            k = k.wrapping_add(2);
        }
        k
    }
}

impl W<V<for<'a> fn(&'a u8) -> &'static u8>> {
    pub fn get(x: u32) -> u32 {
        //~^ NOTE 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
        // RE-PINNED 2026-10-15 (the merge of 2026-10-14): the call into the GENERIC `get`
        // no longer carries a runtime-checked row (the merged tree composes that body,
        // which cannot panic: `wrapping_add` in a loop), so the file builds; still no
        // termination row (one obligation, the `x - 1`), which is this file's subject.
        if x == 0 {
            return 0;
        }
        W::<V<for<'a> fn(&'a u8) -> &'a u8>>::get(x - 1)
    }
}
