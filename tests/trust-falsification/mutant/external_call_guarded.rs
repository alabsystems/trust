#![crate_type = "lib"]
// MUTANT of proved/external_call_guarded.rs: replace the exhaustive match with
// `o.unwrap()`. `Option::unwrap` is an UNMODELED EXTERNAL CALL — its body lives in
// core, is not analyzed, and is not on the trusted-total allowlist — that PANICS
// when `o` is `None`. Before the #47 fix this passed under the default strict policy as a
// FALSE PROOF: the function's only panic risk is inside the call, so its public
// bundle was empty and the native typed-TrustIr lowering failure read as
// "vacuously clean". The verifier MUST now refuse it (exit 1): an unmodeled
// external call whose panic-freedom cannot be established fails closed.
pub fn external_call_guarded(o: Option<u32>) -> u32 {
    o.unwrap()
}
