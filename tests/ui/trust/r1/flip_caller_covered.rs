//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ build-pass
// R1 capability alarm: `helper`'s division-by-zero obligation is unprovable in
// isolation, but every caller establishes `divisor != 0` (here the sole call
// `helper(10, 5)`). The `build-pass` expectation is MET: the router
// supplies a sealed,
// kernel-replayed closed-world proof capability. It must never pass by minting a
// reusable KernelCertified verdict from caller metadata alone.
fn helper(x: u32, divisor: u32) -> u32 {
    x / divisor
}
fn main() {
    let _ = helper(10, 5);
}
