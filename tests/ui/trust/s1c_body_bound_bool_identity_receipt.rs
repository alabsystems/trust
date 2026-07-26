//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ check-fail
//! Task #23 Slice 1 receipt control: unlike the integer Ge fixture, this Bool
//! identity has no Clean arithmetic/source proof for the original placeholder
//! marker. The compiler-authenticated typed proposition names the return `_0`;
//! the body-bound finalizer normalizes it to `result` and derives
//! `let result = flag in result == flag`.
//!
//! Since the TCB closure work (docs/design/2026-07-25-tcb-closure-plan.md
//! step 1) that derived claim is re-derived in the Clean kernel rather than
//! taken from the adapter: `flag = flag` is closed by `Eq.refl`, so the marker
//! seals `BodyBoundKernelCertified` and the report names the kernel re-check.
//! The live Trust-WP receipt is still required to enter the lane — it is what
//! binds the claim to this row — so this fixture remains the receipt control it
//! always was; the reason line is what changed.
//!
//! The strict build still fails on separate fresh rows that remain Unknown.
//! That separation is intentional: the report must show the marker itself as
//! proved without allowing its private receipt to leak authority to any other
//! row.
pub fn bool_identity(flag: bool) -> bool ensures result == flag { flag }
//~^ ERROR strict verification failed
//~| NOTE [postcond] PROVED (trust-certify-body-bound-kernel-recheck): body-bound ensures re-derived and kernel-checked by trust-certify
