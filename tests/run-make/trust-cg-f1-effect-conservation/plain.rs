//! The F1 positive control: no effect is lost, so the gate refuses nothing and the trust-ir
//! frontend completes every reachable function (the Part A F1 control's shape).
#[inline(never)]
pub fn half(x: u64) -> u64 {
    x ^ 0x55
}

#[unsafe(no_mangle)]
pub extern "C" fn effect_conservation_plain_program() -> u64 {
    half(5) ^ 7
}
