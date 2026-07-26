#![crate_type = "lib"]
#![feature(register_tool)]
#![register_tool(trust)]
// SUPERIORITY (verified codegen / trust-cg lane): stock rustc/LLVM codegen is
// UNVERIFIED. `#[trust::verified_codegen]` lowers the function to trust-cg's
// verified LIR, emits the machine code, and proves the emitted bytes compute the
// function's IR semantics on every input. A straight-line scalar arithmetic
// function is inside the fragment where that proof is reachable.
#[trust::verified_codegen]
pub fn add(x: u32, y: u32) -> u32 { x.wrapping_add(y) }
