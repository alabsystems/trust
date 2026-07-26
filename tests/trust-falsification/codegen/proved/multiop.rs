#![crate_type = "lib"]
#![feature(register_tool)]
#![register_tool(trust)]
// SUPERIORITY (verified codegen, SEMANTIC): a multi-operation scalar function.
// Trust lowers it to trust-cg LIR, emits real machine code, decodes the emitted
// bytes, and discharges equality between their machine semantics and the
// semantics auto-derived from the IR — for every input. A lowering that altered,
// dropped, or added an arithmetic operation is refuted by a concrete
// counterexample. Stock rustc/LLVM codegen makes no such claim.
#[trust::verified_codegen]
pub fn poly(x: u32, y: u32) -> u32 {
    x.wrapping_mul(y).wrapping_add(x).wrapping_sub(y)
}
