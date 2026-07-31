//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type=lib
//@ rustc-env:TRUST_MONITOR_REPORT=1
//@ normalize-stderr: "\n\n$" -> "\n"
//@ build-pass
//! §1.1 per-clause monitored-status EVIDENCE sweep (`TRUST_MONITOR_REPORT=1`):
//! for each `requires`/`ensures` clause the sweep reports whether a CERTIFIED
//! runtime monitor exists (a Bool decision with a kernel-checked
//! `monitor = true <-> P` certificate) — per-clause evidence only, never a
//! verdict, so the build outcome is identical to the same clauses without the
//! env var. Clause shapes are copied from the green native_clause_semantics.rs
//! fixture so verification outcomes are unchanged. Over `u64` the machine-int
//! equality certifies a monitor (monitored, via UInt64.decEq +
//! of_decide_eq_true); the signed `i32` lane uses an equivalent exact
//! machine-int decision certificate, so it is monitored as well. Together
//! they pin both signed and unsigned monitor carriers; neither status is a
//! runtime-check verdict (design §1.1). The verification-report
//! annotations are deliberately LOOSE (no proved/unknown counts): this fixture
//! pins the MONITOR notes; prover capability for these obligations is pinned
//! by the native_clause_semantics fixtures and churns independently.

pub fn f_machine(x: u64) -> u64
    ensures result == x
    //~^ NOTE contract clause #0 (Ensures) is monitored: a kernel-certified runtime monitor exists
    //~^^^ NOTE Trust verification:
    //~| NOTE of which 1 kernel-certified
{
    x
}

pub fn identity(x: i32) -> i32
    ensures result == x
    //~^ NOTE contract clause #0 (Ensures) is monitored: a kernel-certified runtime monitor exists
    //~^^^ NOTE Trust verification:
    //~| NOTE of which 1 kernel-certified
{
    x
}
