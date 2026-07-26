// Trust test: float addition overflow to infinity -- safe variant (no obligation row)
// VcKind: FloatOverflowToInfinity { op: BinOp::Add, operand_ty: Ty::Float { width: 64 } }
// Expected: FloatOverflowToInfinity ABSENT
// The finite-literal addition is constant-folded before VC generation, so the
// build carries no FloatOverflowToInfinity row at all — and under the typed
// grammar absence is not PROVED. ABSENT is a generation assertion, not a proof
// claim. The overflow-to-infinity obligation itself is alive and
// caught by the buggy pair verify_float_overflow.rs (FAILED).
// Safe pattern: literal finite operands cannot overflow to infinity.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn float_add_safe() -> f64 {
    1.0 + 2.0 // SAFE: finite literals cannot overflow to infinity
}

fn main() {
    let _ = float_add_safe();
}
