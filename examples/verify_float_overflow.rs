// Trust test: float addition overflow to infinity
// VcKind: FloatOverflowToInfinity { op: BinOp::Add, operand_ty: Ty::Float { width: 64 } }
// Expected: FloatOverflowToInfinity(Add) UNKNOWN
// Current expectation: fail-closed unknown, exit 1.
//   The trust-mc typed-CHC lane still REFUTES this VC (a and b near f64::MAX),
//   but the fieldless ChcPdrSolveStatus::Refuted is demoted to unknown at tip:
//   the 47ffee63479 merge resolved trust-bmc to the strict side and dropped the
//   b62 `bundle_is_certified_havoc_free` Refuted->Failed arm (a bundle-level
//   producer flag is forgeable; pinned by trust-bmc's
//   direct_typed_chc_reachable_error_refutation_is_demoted_to_unknown), and no
//   other lane can refute float kinds (`InProcessAyBackend::can_handle` never
//   admitted FloatOverflowToInfinity, so the v1/ay bridge dispatch returns
//   "no backend can handle this VC" even though a direct ay solve is SAT with
//   a model). "FloatOverflowToInfinity(Add) FAILED" becomes assertable again
//   once a sound refutation lane lands: trust-mc-core Refuted{model} + replay
//   validation, or the per-obligation bound concreteness certificate
//   (trust-bmc extension-path note at the refutation soundness gate).
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
