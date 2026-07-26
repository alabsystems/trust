#![crate_type = "lib"]
#![feature(register_tool)]
#![register_tool(trust)]
// SOUNDNESS REGRESSION (strict-mode false proof, found by the adversarial false-proof
// hunt). `t` is moved into a LOCAL tuple `(t, 0)` that is then DROPPED at scope end — `t`'s
// destructor runs INSIDE the function (a silent drop), NOT a handoff. The slot-liveness
// check alone saw the move-out and wrongly reported PROVED (in DEFAULT and STRICT). The
// `param_resource_dropped` taint+Drop check now reports Leaked, so Trust REJECTS this. If
// it ever PROVES again, the silent-drop-via-aggregate hole has regressed.
pub struct Token(u32);
// A real resource: dropping it runs a destructor (here a no-op, but its presence is what
// makes the silent drop observable / meaningful — and emits the MIR `Drop` terminator the
// linearity check keys on).
impl Drop for Token {
    fn drop(&mut self) {}
}
#[trust::must_consume]
pub fn pack_and_drop(t: Token) -> u32 {
    let pair = (t, 0u32);
    pair.1
}
