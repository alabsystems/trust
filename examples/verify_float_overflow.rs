// Trust test: float addition overflow to infinity
// VcKind: FloatOverflowToInfinity { op: BinOp::Add, operand_ty: Ty::Float { width: 64 } }
// Expected: FloatOverflowToInfinity(Add) FAILED
// The refutation is a witnessed counterexample, exit 1.
//   This example previously asserted a fail-closed unknown: the fieldless
//   `ChcPdrSolveStatus::Refuted` was demoted to unknown, and no other lane could
//   refute float kinds (`InProcessAyBackend::can_handle` never admitted
//   FloatOverflowToInfinity). The sound refutation lane that header named as its
//   precondition has since landed — trust-mc's `acyclic_direct_smt_decision`
//   composes a concrete satisfiable derivation of `error` and returns
//   `refuted_with_witness(ChcPdrCexVerification::DirectSmtModel)`, guarded by
//   `fail_closed_lowering_sites` so an admission failure can never masquerade as
//   a program trap (first-party/trust-mc/trust-mc-driver/src/native.rs). The row
//   now carries solver `trust-full-verifier`, a `Counterexample` artifact digest,
//   and the diagnostic "direct SMT confirmed a satisfiable typed query fact;
//   refuted obligation via acyclic error derivation before PDR".
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn float_add(a: f64, b: f64) -> f64 {
    a + b // BUG: produces +Inf when a + b > f64::MAX
}

fn main() {
    // Argv-derived (unknown) inputs: safe constants here would let the R1
    // caller-propagation lane prove the whole program safe and discharge the
    // isolated refutation this example exists to demonstrate.
    let n = std::env::args().len() as f64;
    let _ = float_add(n, n);
}
