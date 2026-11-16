// Part A′'s positive control: no shim, a body trust-cg's MIR frontend proves and ships under the
// strict output gate, so the defined-symbol check that would see a shipped shim is not vacuous.
#[unsafe(no_mangle)]
pub extern "C" fn ctl(x: u64) -> u64 {
    x ^ 1
}
