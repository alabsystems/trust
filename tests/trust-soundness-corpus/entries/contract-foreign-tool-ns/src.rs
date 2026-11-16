// trust-soundness-corpus entry `contract-foreign-tool-ns` (CONTRACT-NS-1). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
#[clippy::requires = "__trust_lowered_compiler_contract__:x < 100"]
pub fn f(x: u32) -> u32 {
    x + 4_294_967_000
}

// Twin: the precondition as code.
pub fn f_guarded(x: u32) -> u32 {
    if x < 100 { x + 4_294_967_000 } else { 0 }
}
