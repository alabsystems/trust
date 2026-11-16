//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! CLOSED 2026-09-19. The filename keeps `KNOWN_GAP` on purpose: this file was
//! the gap's own record, and renaming it would break the trail from the
//! `docs/KNOWN_HAZARDS.md` "EMPTY bridged inventory" note that points here.
//!
//! WHAT IT USED TO RECORD. This body built EXIT 0 carrying one
//! `native-verification-gap` row (`outcome: unknown`, invisible in human output)
//! and no verdict for the call at all. The bridge lowers the fn-pointer call to
//! `CallIndirect` plus its may-panic assert, no native engine dispatches it, and
//! the strict gate's early returns let the empty inventory through. The note
//! above said "a verify-off dependency exporting `pub static F: fn() = boom;`
//! reaches user code this way with nothing reported" — that sentence was built
//! and run (`scripts/fn_pointer_witness.sh`): the consumer compiled green on the
//! VERIFYING lane and the binary panicked with exit 101.
//!
//! WHY IT IS CLOSED, and why this is conformance rather than a new policy.
//! `trust_types::TRUST_INDIRECT_CALLEE_PATH` — the reserved `@trust-indirect-callee`
//! name extraction stamps on exactly these calls — already stated the contract:
//! "A consumer that cannot model an open dispatch must fail closed on it exactly
//! as it would on any other callee whose body is absent." The strict gate now
//! does, via `function_has_unresolved_indirect_call`.
//!
//! WHY NOT THE TIGHTENING THAT WAS TRIED AND ABANDONED. A gate keyed on
//! `zero_obligation_undischarged_call_funcs` broke five of the designed
//! discharges, because their calls are discharged by a reliance CERTIFICATE
//! rather than the registry, so that set names them too. Every one of those is a
//! `dyn`/trait dispatch with a real `DefId`; none is an indirect call. Keying on
//! the ABSENCE of a `DefId` separates the hole from every designed discharge
//! structurally, with no evidence channel to build and nothing to keep in step.
//! Measured across all 907 `tests/ui/trust` cases: this file and
//! `static_str_write_fmt_assumed_total_second_pointer_hop_control.rs` were the
//! only two to move, and the second was then preserved by recognising a
//! statically REIFIED pointer as resolvable.
//!
//! STILL ADMITTED, and it is a different thing: `let f: fn() = g; f()` verifies,
//! because the target is statically `g` and `g` is verified as its own root.
//! `tests/fn-pointer-witness/fragment/f5_statically_known_pointer.rs` is that
//! boundary. The contrasts `pub fn call(f: &dyn Fn()) { f() }` and
//! `pub fn call<F: Fn()>(f: F) { f() }` refused before this change and refuse now.
pub fn call(f: fn()) {
    //~^ ERROR Trust strict verification failed
    f()
}
