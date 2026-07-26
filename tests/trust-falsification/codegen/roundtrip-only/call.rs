#![crate_type = "lib"]
#![feature(register_tool)]
#![register_tool(trust)]
// HONESTY CONTROL: a call is inside trust-cg's lowerable fragment but outside
// the byte-level output-preservation gate's — with no callee environment, both
// the IR interpreter and the machine-side executor fail closed on the call.
// Trust must say so, reporting that only the structural round-trip check held.
// Without this fixture, a gate that stopped machine-checking entirely and fell
// back to the structural comparison everywhere would still look green.
#[trust::verified_codegen]
pub fn via_call(x: u32) -> u32 {
    helper(x)
}

#[inline(never)]
fn helper(x: u32) -> u32 {
    x.wrapping_add(1)
}
