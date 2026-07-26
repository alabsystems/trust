//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//! Trust #14 soundness regression. A native first-class `requires` clause binds
//! to the ENTRY PARAMETER — recovered from the HIR signature when
//! `var_debug_info` is absent at low `-Cdebuginfo` (locals `1..=arg_count` are
//! the parameters by MIR construction). The recovery names ONLY the parameter
//! local, never a body local, so it must not leak the assumption onto a local
//! that shadows the parameter's name: here `x` is re-bound to `u64::MAX` and
//! `x + 1` overflows, so the precondition `x < 10` (about the *parameter*) must
//! not discharge the *shadow*'s overflow. The build MUST fail — the overflow
//! obligation stays refuted, never falsely proved. If signature-recovery ever
//! named the shadow local too, the overflow could false-PROVE; this fixture is
//! the guard. (Manual evidence at the fix: the overflow reports
//! `arithmetic_safety ... without a proof; counterexample`, i.e. refuted.)

fn f(x: u64) -> u64
    requires x < 10
{
    let x = u64::MAX;
    x + 1
}

fn main() {
    let _ = f(3);
}
