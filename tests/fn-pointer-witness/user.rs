//! A GREEN BUILD HERE IS THE FINDING, not a pass.
//!
//! Built with `-Ztrust-verify=on` — the VERIFYING lane — this exits 0, and the
//! resulting binary panics at runtime with exit 101. `user::call`, the function
//! that actually contains the indirect call, receives NO obligation row at all;
//! only `main` gets warnings.
//!
//! The bridge lowers the fn-pointer call to `CallIndirect` plus a may-panic
//! assert, no native engine dispatches it, and the strict gate's early returns
//! in `abort_on_full_verification_failure` let the empty inventory through —
//! the `docs/KNOWN_HAZARDS.md` "EMPTY bridged inventory" hole.
//!
//! `tests/ui/trust/policy_b/fn_pointer_call_is_silently_unverified_KNOWN_GAP.rs`
//! records the single-crate half of this in prose. This is the end-to-end
//! witness: a green build of a panicking program, reachable with no `unsafe`,
//! no attribute, and no exotic flag on the crate under test.
//!
//! Contrast — BOTH of these refuse today, so the fragment boundary is narrow:
//!     pub fn call(f: &dyn Fn()) { f() }
//!     pub fn call<F: Fn()>(f: F) { f() }
extern crate dep;
pub fn call(f: fn()) { f() }
fn main() { call(dep::F); }
